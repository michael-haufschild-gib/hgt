# Every critical projective horizon has full symmetric monodromy

- **ID:** `projective-horizon-full-symmetric-monodromy`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ALL-RANK BRANCHED-COVER TOPOLOGY
- **Scientific status:** `[PROVED ON PAPER] [NOVELTY PROVISIONAL] [SIGNIFICANT]`
- **Formal status:** conormal-displacement uniqueness core formalized
- **Parents:** `projective-horizon-irreducible-simple-ramification`,
  `projective-horizon-rank-one-full-monodromy`,
  `projective-horizon-reversal-self-legendre-tower`
- **Lane:** source-pure hypertranscendental geometry; static monodromy

## Theorem

Let `K` be an algebraically closed characteristic-zero field, let `m,n>=1`, set `L=m+n`, and
consider the critical raw/reciprocal tail map

```text
Phi_(m,n): X(t)=sum_(i=0)^(L-1)x_i t^i  |->
  ((x_m,...,x_(L-1)),(y_n,...,y_(L-1))),
Y=X^-1 mod t^L.                                            (1)
```

Restrict to the open chart

```text
x_0 p_m q_n != 0,       p_m=x_m, q_n=y_n.                  (2)
```

The map is generically finite of degree

```text
D=choose(L,m).                                              (3)
```

Its geometric monodromy group on the `D` critical states is

```text
Mon_geom(Phi_(m,n))=S_D.                                   (4)
```

Moreover, the irreducible rectangular-Schur ramification divisor maps generically one-to-one to
the branch divisor.  A meridian around its smooth generic point acts as one transposition, not as
a product of several transpositions.

## Proof

### 1. Finite cover and one ramification component

The critical multiplicity theorem gives `(3)`.  Its biprojective boundary exclusion shows that,
under `(2)`, no state escapes to infinity, so the critical map is finite after restricting to the
stated open base.

The ramification theorem identifies the Jacobian divisor with the rectangular Schur polynomial,
proves that it is irreducible and reduced, and proves generic corank one.  Thus its generic points
are simple folds.  What remained open was whether several such folds lay over one generic branch
value.

### 2. The exact Lagrangian conormal remembers the tangent pair

Write a state as

```text
X=A+P,   deg A<m,   ord P>=m,
Y=B+Q,   deg B<n,   ord Q>=n.                              (5)
```

At a ramification point, a vertical tangent is a nonzero low pair `(U,V)` satisfying

```text
deg U<m,   deg V<n,   UY+XV=0 mod t^L.                     (6)
```

The inversion graph is Lagrangian for

```text
omega((dX,dY),(dX',dY'))=[t^(L-1)](dX dY'-dX' dY).         (7)
```

Pairing `(U,V)` with a general tangent and using the low-degree bounds gives the branch conormal

```text
eta_(U,V)(delta P,delta Q)
  =[t^(L-1)](U delta Q-delta P V).                         (8)
```

The pairing in `(8)` is perfect: the coefficients of `U` pair in reverse order with
`delta q_n,...,delta q_(L-1)`, and the coefficients of `V` pair in reverse order with
`delta p_m,...,delta p_(L-1)`.  Therefore the projective conormal line at the branch value uniquely
determines the projective tangent pair `(U,V)`.

### 3. A generic branch value has only one ramified state

Suppose two generic ramified states `(X,Y)` and `(X',Y')` lie over the same smooth branch value.
The branch has one conormal line, so part 2 lets us scale their kernel pairs to the same `(U,V)`.
Because the tails agree,

```text
D_0=X'-X,    deg D_0<m,
E_0=Y'-Y,    deg E_0<n.                                   (9)
```

Subtracting the two tangent equations gives the exact polynomial syzygy

```text
D_0 V+E_0 U=0.                                             (10)
```

At the generic Schur fold, the endpoint coefficient `U(0)` is nonzero.  Its vanishing is a proper
cofactor locus inside the irreducible determinant divisor: the relevant `(m-1) x (m-1)` Toeplitz
cofactor is a nonzero Schur polynomial and cannot be divisible by the larger irreducible determinant.
The degree-zero part of `(6)` then also makes `V(0)` nonzero.

Consequently `U` and `V` are coprime at the generic fold.  Indeed, any common factor `g` has
`g(0)!=0`, hence is invertible modulo `t^L`.  Dividing `(6)` by `g` would produce another low tangent
pair.  Generic corank one makes it proportional to `(U,V)`, which forces `g` to be constant.

Euclid's lemma now turns `(10)` into

```text
D_0=C U,       E_0=-C V.                                   (11)
```

for a polynomial `C`.

Subtract the two inverse identities and use the tangent identity `(6)`.  With `(11)`, the result
can be written in either of the equivalent forms

```text
C U (Y+Y')=0 mod t^L,
C V (X+X')=0 mod t^L.                                     (12)
```

If the states were distinct, `C U` would be nonzero of degree below `m`.  But the common marked
tail gives

```text
[t^n](Y+Y')=2q_n !=0.                                     (13)
```

The product in the first equation of `(12)` therefore has a nonzero coefficient strictly below
`m+n=L`, by multiplicativity of polynomial trailing degree.  This contradicts `(12)`.  Hence the
states coincide.  The ramification-to-branch degree is one, and generic branch inertia is a single
transposition.

### 4. The transpositions cannot preserve hidden blocks

Let `G<=S_D` be geometric monodromy and let `H` be the normal subgroup generated by meridians around
the irreducible Schur branch.  Part 3 makes those meridians transpositions.  A group generated by
transpositions is a product of symmetric groups on the connected components of its transposition
graph.  Its orbits are therefore a block system for `G`.

If there were more than one block, the induced block cover would be a nontrivial finite etale cover
of the whole parameter chart

```text
S=(G_m)^2 x A^(L-2),                                      (14)
```

because the only interior branch inertia lies in `H`.  For `m,n>=2`, no such intermediate cover
can occur inside the rational source function field.  Indeed, finite etale covers of `(14)` over an
algebraically closed characteristic-zero field are torus Kummer covers.  Every nontrivial one has a
cyclic quotient of the form

```text
z^r=p_m^a q_n^b,        (a,b) not both 0 mod r.             (15)
```

In the source field, the prime divisor `x_m=0` has valuation

```text
v_m(p_m)=1,   v_m(q_n)=0,                                  (16)
```

because `m>=2` and the reciprocal coefficient `y_n` remains generically nonzero when `x_m=0`.
The triangular inverse-coordinate divisor `y_n=0` likewise has

```text
v_n(q_n)=1,   v_n(p_m)=0.                                  (17)
```

Applying `(16)--(17)` to `(15)` forces `r|a` and `r|b`, a contradiction.  Thus the block cover is
trivial, `H` is transitive, and a transitive group generated by transpositions is `S_D`.

When `min(m,n)=1`, the separately proved rank-one eliminant theorem gives `S_L=S_D`, including the
exceptional `(1,1)` Kummer presentation.  This completes all cases and proves `(4)`.  `QED`

## What the theorem rules out

At the pure-tail point the `D` states are visibly `m`-subsets of `L` roots, and the subgroup `S_L`
acts through that labeling.  The theorem proves that this label is not conserved by arbitrary tail
deformation when `m,n>=2`: the generic monodromy expands to the full symmetric group on all
`choose(L,m)` states.  There is no hidden spectral polynomial whose root subsets globally label the
all-tail cover, no particle-number block system beyond the fixed cardinality of the fiber, and no
generic complement pairing at `m=n`.

The structures that survive arbitrary tails are exactly the ones proved earlier: the exact
Lagrangian graph, reversal Legendre duality, the irreducible Schur caustic, and the Q-system of its
mass determinants.

## Exact reconstruction-complexity transition

Full symmetric monodromy has two immediate sharp consequences.

First, the natural `S_D` action is primitive, so the generic finite horizon map has no nontrivial
factorization through a lower-degree connected cover.  Critical reconstruction is algebraically
atomic even though its ramification determinants satisfy an integrable Q-system.

It also has no rational section when `D>1`: a finite-tail algebraic formula cannot choose one
critical state consistently over the generic parameter space.  Any state selector must add
non-algebraic continuation data or source-specific structure outside the universal finite tails.

Second, the generic state equation is solvable by radicals exactly when `S_D` is solvable, hence
exactly when `D<=4`.  Since `D=choose(m+n,m)`, the only positive horizon pairs in this radical regime
are

```text
(1,1), (1,2), (2,1), (1,3), (3,1).                         (18)
```

Every genuinely two-sided horizon `m,n>=2` has `D>=choose(4,2)=6` and is generically not solvable by
radicals.  Rank-one horizons cross the same boundary at total depth `m+n=5`.  Thus determinant-level
integrability and state-level algebraic solvability are rigorously different properties of the
constraint.

## Physical and topological meaning

Finite horizon vacua are locally distinguishable but globally unlabelled.  Adiabatic continuation
in the static observation-parameter space can realize every permutation of the critical states.
The pure fermionic occupation labels are a symmetry-enhanced boundary coordinate system, not
fundamental particles.

The physical object is therefore a maximally braided exact-Lagrangian polarization atlas:

```text
local vacua             = sheets of a finite Lagrangian projection,
massless horizon        = one irreducible Schur fold,
global continuation     = the full symmetric group on all sheets,
all polarization masses = one nonvanishing Q-system.       (19)
```

Its first genuinely two-sided finite observation already has six globally unlabelled vacua and an
Abel--Ruffini obstruction to generic radical reconstruction.  This is static algebraic complexity,
not dynamical chaos.

This is topology of a static constraint family.  It supplies no time variable, Hamiltonian,
quantization, black-hole interior, or Born rule.

## Novelty and significance audit

Generic polynomial monodromy, fold conormals of Lagrangian maps, transposition graphs, torus etale
covers, and Kummer valuations are classical ingredients.  The candidate new result is their exact
conjunction for every reciprocal-jet horizon map: the rectangular Schur ramification component has
branch degree one and forces full `S_(choose(m+n,m))` monodromy at every rank.

The conclusion is strictly stronger than the classical pure Grassmannian/subset model and refutes
the most plausible invariant-block alternative.  A targeted literature audit found generic sparse
system monodromy and Grassmannian Bethe/subset actions, but no theorem for this all-tail reciprocal
horizon cover.  Novelty remains provisional pending expert review.

This clears the lane's stated all-rank monodromy target and gives a genuine global classification of
the finite vacuum topology.  It is significant new knowledge for the proposed hypertranscendental
geometry.  It still does not classify hypertranscendental functions themselves or create an
external application at the scale required by the user's Fields-Medal completion bar.

## Primary literature boundary checked

- Esterov proves full symmetric monodromy for general reduced irreducible sparse square systems,
  but the reciprocal-tail coefficients here form a special constrained family rather than the
  independently generic coefficient family of that theorem:
  <https://arxiv.org/abs/1801.08260>.
- Pirola--Schlesinger prove full symmetric monodromy for general linear projections of projective
  curves.  The horizon map is a fixed mixed-coordinate projection of an exact reciprocal graph,
  so their uniform-position theorem does not state this result:
  <https://arxiv.org/abs/math/0312375>.
- Gorbounov--Korff's equivariant Grassmannian Bethe theory supplies the classical pure
  `m`-subset/Bethe-vector comparison and an `S_L` action.  The theorem here proves that arbitrary
  reciprocal tails unfold beyond that action to `S_(choose(L,m))`:
  <https://arxiv.org/abs/1402.2907>.

## RH impact

For zeta, every finite critical horizon cover has generic full symmetric monodromy.  This is a
useful no-go: no state or subset label built solely from the universal reciprocal horizon geometry
can carry an RH orientation, and no finite-tail rational formula can select a preferred
reconstruction sheet.  Any RH-relevant reduction of monodromy must come from the Euler source,
functional equation, an infinite-depth limit, or a real/positive structure absent from the
universal cover.  The theorem does not imply RH.

## Formal verification

`ProjectiveHorizonExactLagrangian.lean` formalizes the perfect reversed coefficient/cotangent
pairing and Lagrangian isotropy underlying `(8)`.
`ProjectiveHorizonRamificationUniqueness.lean` formalizes the decisive impossibility in
`(11)--(13)` as `criticalHorizon_sharedConormal_displacement_eq_zero`.
`ProjectiveHorizonCriticalMultiplicity.lean` supplies the trailing-degree contradiction and the
degree `(3)`; its strongest truncation theorem derives the second factor's nonzeroness directly
from the marked nonzero coefficient.  The Schur irreducibility, generic conormal geometry, etale-cover classification, and
permutation-group closure are paper-level.

Only targeted leaf checks are used; no full build is run.

## Log

- 2026-08-01 — **The conormal pairing and the uniqueness of a ramified state are formalized.**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonConormalPairing.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `coeff_mul_X_pow_top` — the top-coefficient pairing of a polynomial with a tail monomial reads off
  one coefficient of that polynomial, `(U * X^(L-1-i)).coeff (L-1) = U.coeff i`, which is the
  reversal described after `(8)`.

  `eq_zero_of_pairing_eq_zero` — **the pairing is perfect**: a polynomial of degree below `m` that
  pairs to zero against every tail monomial `t^j`, `n ≤ j < L`, vanishes.  This is step 2: the
  projective conormal line at the branch value determines the projective tangent pair, because the
  functional determines the coefficients of `U` one at a time.

  `exists_cofactor_of_syzygy` — the syzygy `(10)` against a coprime pair factors through a single
  cofactor, `D = C U` and `E = -(C V)`, which is `(11)`; the proof is Euclid's lemma through
  `IsCoprime.dvd_of_dvd_mul_right`, and the second component follows from cancelling `U`.

  `eq_zero_of_syzygy_of_marked_coeff` — step 3's conclusion: with the marked tail coefficient
  `(13)` nonzero, a difference of degree below `m` whose product with the marked series vanishes
  through order `L-1` is itself zero, and then so is the second difference.  The surviving-coefficient
  input is the trailing-degree theorem `not_all_low_mul_coeff_zero_of_coeff_ne_zero` already proved
  for the multiplicity card.

  What stays paper-level: the irreducibility and reducedness of the rectangular Schur divisor, the
  classification of finite etale covers of `(14)` as torus Kummer covers, and the identification of
  the meridian action.  The final group-theoretic step is available in mathlib —
  `Equiv.Perm.swap_mem_closure_isSwap` gives that a subgroup generated by transpositions contains
  `swap x y` exactly when `x` and `y` share an orbit, so a transitive such subgroup is the full
  symmetric group.

- 2026-08-01 — **Step 4's group theory is formalized.**
  `formal/GaloisForLFunctions/HTGeometry/TranspositionTransitive.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `eq_top_of_isSwap_of_transitive` — a subgroup of a finite symmetric group generated by
  transpositions and acting transitively is the whole symmetric group;
  `eq_top_of_isSwap_of_orbit_eq_univ` — the same from a single orbit being everything;
  `eq_top_of_meridian_isSwap_of_orbit_eq_univ` — the conclusion `(4)` in the form the proof uses:
  once the meridian subgroup is generated by transpositions and has one orbit, the ambient monodromy
  group is the full symmetric group on the fiber.

  Two parts of step 4 need no construction here.  That the orbits of a normal subgroup form a block
  system is mathlib's `MulAction.IsBlock.orbit_of_normal`; and that a subgroup generated by
  transpositions contains `swap x y` exactly when `x` and `y` share an orbit is mathlib's
  `swap_mem_closure_isSwap`, which is what makes the theorems above three-line proofs rather than a
  transposition-graph development.

  So the group-theoretic skeleton of `(4)` is complete.  What remains for the card is geometric: the
  irreducibility and reducedness of the rectangular Schur ramification divisor, and the
  classification of finite etale covers of `(G_m)^2 x A^(L-2)` as torus Kummer covers, which is what
  forces the block system to be trivial.  The Kummer step `(15)--(17)` is, once that classification
  is granted, the arithmetic observation that two divisors seeing `p_m` and `q_n` separately force
  `r | a` and `r | b`.

- 2026-08-01 — **The radical-regime classification `(18)` is proved.**
  `formal/GaloisForLFunctions/HTGeometry/CriticalHorizonRadicalRegime.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `criticalHorizonMultiplicity_le_four_iff` — the critical multiplicity is at most four exactly when
  one depth is one and the other at most three; `criticalHorizonMultiplicity_le_four_iff_mem` — the
  same as the explicit list `(1,1), (1,2), (2,1), (1,3), (3,1)`, which is `(18)`;
  `not_isSolvable_perm_criticalStates` — for `m,n ≥ 2` the symmetric group on the critical states is
  **not solvable**, through the six-state lower bound already proved for the multiplicity card and
  mathlib's `Equiv.Perm.not_solvable`.

  What this establishes is the group-theoretic half of the solvability statement: outside the five
  listed pairs the symmetric group on the fiber is not solvable.  Reading that as "the generic state
  equation is not solvable by radicals" still uses `(4)`, whose remaining inputs are the Schur
  divisor's irreducibility and the etale-cover classification.

  Note that the converse half — that `S_4` and below **are** solvable — is not in mathlib and is not
  added here: it would be a derived-series computation on the twenty-four element group, and the card
  only needs the negative direction.

- 2026-08-01 — **The division step of the coprimality argument is formalized.**
  `formal/GaloisForLFunctions/HTGeometry/HorizonTruncationCancel.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `isCoprime_X_of_coeff_zero_ne_zero` — a polynomial with nonzero constant term is coprime to the
  variable; `dvd_of_mul_dvd_of_coeff_zero_ne_zero` — such a polynomial may therefore be cancelled
  from a divisibility by a power of the variable, which is the precise content of "invertible modulo
  `t^L`"; `tangent_relation_of_common_factor` — if the two components of a vertical tangent pair
  share a factor with nonzero constant term, the quotients satisfy the **same** truncated relation
  `(6)`, so they are again a low tangent pair.

  That is the step "dividing `(6)` by `g` would produce another low tangent pair" of part 3, without
  the geometric input.  What the argument still takes from geometry is generic corank one, which
  makes the new pair proportional to the old and so forces `g` to be constant.

  The lemma is stated for a general truncation `X^L ∣ U B + A V`, so it also serves the boundary
  exclusions of the multiplicity card and the postcritical rigidity card, which cancel the same kind
  of factor.

- 2026-08-01 — **The Schur divisor's irreducibility and reducedness are no longer paper-level.**
  `formal/GaloisForLFunctions/HTGeometry/BlockComplementaryMinor.lean`,
  `DualRectangularSection.lean`, `SchurCofactorLocus.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `irreducible_det_rectangularSchurToeplitz` — the rectangular Schur section is irreducible at
  **every** pair of parameters; `squarefree_det_rectangularSchurToeplitz` — hence squarefree, so the
  ramification divisor is reduced; `not_dvd_det_submatrix_rectangularSchur` — the section does not
  divide its corner cofactor, which is generic corank one in its algebraic form: the cofactor locus
  is a proper closed subset of the divisor.

  Those are the three geometric inputs this card has repeatedly recorded as paper-level.  The route
  to the first was the missing complementary-minor formula: mathlib has none, so
  `det_toBlocks₂₁_eq` proves the block form directly, and with the two coefficient families forming
  inverse triangular matrices it exchanges the two parameters of a section.  That removes the
  restriction `m ≤ n` under which the corner-expansion induction had proved irreducibility, and the
  cofactor argument then needs irreducibility at the *unrelated* pair `(n-1,m-1)`, which only the
  unrestricted statement supplies.

  What remains for `(4)` is the classification of finite etale covers of `(G_m)^2 x A^(L-2)` as torus
  Kummer covers, and the identification of the meridian action.  The group theory (step 4), the
  conormal pairing and state uniqueness (steps 2 and 3), the radical regime `(18)`, and the division
  step of the coprimality argument were already formalized.

- 2026-08-01 — **The Kummer step `(15)--(17)` is formalized, sharply.**
  `formal/GaloisForLFunctions/HTGeometry/TorusKummerExponents.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `dvd_of_kummer_relation` — reading a relation `z ^ r = c * p ^ a * q ^ b` through two
  homomorphisms to the integers, one seeing `p` once and `q` not at all and the other the reverse,
  both vanishing on `c`, gives `r ∣ a` **and** `r ∣ b`.  That is exactly `(16)--(17)` applied to
  `(15)`: the divisor `x_m = 0` and the inverse-coordinate divisor `y_n = 0` see `p_m` and `q_n`
  separately.  `not_exists_kummer_relation` states it as the obstruction: with `(a,b)` not both zero
  modulo `r`, no such relation exists.

  The hypotheses are not vacuous, and the obstruction is sharp.  `TorusUnitGroup` is the unit group
  of the coordinate ring of `(G_m)^2 x A^k` — a constant together with the two monomial exponents —
  with `torusVal₁`, `torusVal₂` the two exponents and `torusGen₁`, `torusGen₂` the two coordinates.
  `torusUnit_eq` decomposes any unit as `(15)`, and `exists_pow_eq_torusUnit_iff` proves **both**
  directions:

  ```text
  (∃ z, z ^ r = u)  ↔  r ∣ (first exponent of u)  ∧  r ∣ (second exponent of u).
  ```

  The reverse direction is where algebraic closure enters: the constant is never an obstruction
  because `IsAlgClosed.exists_pow_nat_eq` supplies its `r`-th root, so the only obstruction is the
  exponent pair.  `not_exists_pow_eq_torusUnit` is the conclusion in the card's shape: a cover with
  a nontrivial exponent pair modulo `r` does not exist, at any constant.

  What this does **not** do is classify the covers.  The step from "finite etale cover of
  `(G_m)^2 x A^(L-2)`" to "cyclic quotient of the form `(15)`" is the etale fundamental group of a
  torus times an affine space, and mathlib has no etale fundamental group at all — that is a
  scheme-theoretic development, not a missing lemma.  What is now formalized is the card's own
  description of the remainder: "once that classification is granted, the arithmetic observation
  that two divisors seeing `p_m` and `q_n` separately force `r | a` and `r | b`."  Granted the
  classification, `(4)` follows from this file together with the already-formalized step 4 group
  theory and the now-proved irreducibility and reducedness of the Schur divisor.

- 2026-08-01 — **The cyclic half of the etale classification, by commutative algebra.**
  `formal/GaloisForLFunctions/HTGeometry/UfdPowerDescent.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The classification step of `(4)` does not have to be approached through the etale fundamental
  group.  For a **cyclic** cover the content is elementary and lives in the unique factorization
  monoid: a radical extension `z ^ r = a` is unramified at a prime exactly when that prime's
  multiplicity in `a` is divisible by `r`, so an everywhere-unramified one has all multiplicities
  divisible, and then

  `exists_associated_pow_of_forall_dvd_count` — the element is associated to an `r`-th power.  The
  factorization multiset has every count divisible by `r`, hence is `r` times a smaller multiset,
  whose product is the root (`Multiset.exists_smul_of_dvd_count`, `Multiset.prod_nsmul`,
  `prod_normalizedFactors`).  `forall_dvd_count_of_associated_pow` is the converse, so the
  divisibility condition is exactly right and not merely sufficient.
  `exists_associated_pow_of_forall_dvd_multiplicity` restates it through `multiplicity` at primes.

  `exists_unit_mul_pow_of_forall_dvd_count` — hence `a = u * g ^ r` with `u` a **unit**: an
  everywhere-unramified radical extension is generated by an `r`-th root of a unit.  This is the
  step that turns a cover of the space into a cover of its unit group, and it needs no schemes.

  `exists_unit_mul_pow_torus_kummer` — combined with the previous file, the cyclic classification:
  given that the units of the base are a constant with two monomial exponents
  (`Rˣ ≃* TorusUnitGroup K`), the radicand is a unit times an `r`-th power, and that unit is itself
  an `r`-th power **exactly** when both of its exponents are divisible by `r`.  So the nontrivial
  unramified cyclic covers are classified by the exponent pair modulo `r`, which is `(15)`, and
  `(16)--(17)` then kill them.

  What is still missing for `(4)`.  Two things, and they are of different kinds.  First, the unit
  group hypothesis is carried as an isomorphism rather than computed: constructing
  `K[x₁^{±1}, x₂^{±1}, x₃, …, x_L]` as a localization and proving its units are constants times two
  monomials is ordinary commutative algebra, and is the next piece to build.  Second, the reduction
  from an arbitrary connected finite etale cover to a **cyclic** one is the abelianness of the etale
  fundamental group; that genuinely needs etale homotopy, which mathlib does not have.  The
  commutative-algebra route above settles everything downstream of that reduction.

- 2026-08-01 — **The unit group of the chart `(14)` is computed.**
  `formal/GaloisForLFunctions/HTGeometry/LocalizationTwoPrimeUnits.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The previous entry left the unit group of the base as a hypothesis.  It is now a theorem.
  `TorusChart K L` is the chart `(14)` presented as a localization — the polynomial ring in `L + 2`
  variables with its first two coordinates inverted — and

  `exists_monomial_of_isUnit_torusChart` — every unit of the chart is a nonzero constant times a
  Laurent monomial in the two invertible coordinates:

  ```text
  u * (x₀ x₁) ^ n = C c * x₀ ^ s * x₁ ^ t,     c ≠ 0.
  ```

  That is exactly the shape of `(15)`, now derived rather than assumed.

  Two steps.  `exists_unit_mul_pow_mul_pow_of_dvd` — in a unique factorization domain a divisor of a
  product of powers of two primes is a unit times powers of those primes; the divisor splits
  (`exists_dvd_and_dvd_of_dvd_mul`) and each factor is handled by `dvd_prime_pow`.
  `dvd_pow_of_isUnit_algebraMap` — an element of the base whose image in the localization is a unit
  divides a power of the inverted element; the inverse is cleared of its own denominator by
  `IsLocalization.Away.surj` and the resulting identity descends through the injectivity of the
  structure map.  Putting the two together, `exists_monomial_of_isUnit_away` gives the general
  statement for any unique factorization domain and any two primes; the chart is the instance
  `p = x₀`, `q = x₁`, where the base units are the nonzero constants
  (`MvPolynomial.isUnit_iff_eq_C_of_isReduced`).

  What remains.  For the full isomorphism `Rˣ ≃* TorusUnitGroup K` used by the previous entry, only
  **uniqueness** of the exponent pair is still missing — that the presentation above is unique, which
  is again unique factorization and is the next piece.  Beyond that the sole remaining input to `(4)`
  is the reduction of an arbitrary connected finite etale cover to a cyclic one, which is the
  abelianness of the etale fundamental group and needs machinery mathlib does not have.

- 2026-08-01 — **The exponents of `(15)` are unique.**
  `formal/GaloisForLFunctions/HTGeometry/LocalizationTwoPrimeUnits.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `eq_of_unit_mul_pow_mul_pow` — in a domain, if a unit times a product of powers of two
  non-associate primes equals another such product, then both exponents and the unit agree.  No
  normalization structure and no factorization multiset is needed: if the first exponents differed,
  cancelling the smaller power of `p` would leave `p` dividing a unit times a power of `q`, and `p`
  divides neither factor — it does not divide a unit, and it does not divide `q` because two
  non-associate primes do not divide one another.  `exponent_eq_of_unit_mul_pow_mul_pow` is that
  step; the second exponent is the same statement with the primes exchanged, and the unit then
  cancels.

  `exponents_unique_away` — the same at the level of the localization, in the cleared form the
  presentation actually takes:

  ```text
  u * (p q) ^ n  = c  * p ^ s  * q ^ t
  u * (p q) ^ n' = c' * p ^ s' * q ^ t'
    ⟹  s + n' = s' + n,   t + n' = t' + n,   c = c'.
  ```

  Cross-multiplying the two presentations and descending through the injectivity of the structure map
  reduces it to the previous theorem.  So the exponent **differences** `s - n` and `t - n` are well
  defined invariants of the unit, which is exactly what makes the two valuations `(16)--(17)` of the
  card well defined on the unit group.

  Together with the previous entry the unit group of the chart `(14)` is now determined: existence of
  the presentation `(15)` and uniqueness of its data.  What is left on this branch is packaging the
  two into the group isomorphism `Rˣ ≃* TorusUnitGroup K` that
  `exists_unit_mul_pow_torus_kummer` consumes — glue between the cleared natural-number form and the
  integer-exponent form, no new mathematics.  Beyond that the sole remaining input to `(4)` is still
  the reduction of a connected finite etale cover to a cyclic one.

- 2026-08-01 — **`(15)--(17)` closed on the actual chart, without the group isomorphism.**
  `formal/GaloisForLFunctions/HTGeometry/LocalizationTwoPrimeUnits.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The previous entry proposed packaging existence and uniqueness of the presentation into
  `Rˣ ≃* TorusUnitGroup K`.  That packaging is unnecessary: the implication the argument actually
  uses follows from the two directly, and the detour through integer exponents disappears.

  `dvd_exponents_of_eq_pow` — if a unit of the localization is an `r`-th power, both of its exponent
  differences are divisible by `r`:

  ```text
  u = w ^ r  ⟹  r ∣ s - n   and   r ∣ t - n.
  ```

  Raising the root's presentation to the `r`-th power presents the element itself, with data
  `(c'^r, r s', r t', r n')`; uniqueness (`exponents_unique_away`) matches it against the element's
  own presentation, giving `s + r n' = r s' + n` and `t + r n' = r t' + n`, so each exponent
  difference is `r` times the root's.

  `dvd_exponents_of_eq_pow_torusChart` — the same on the chart `(14)` itself, with `p = x₀`,
  `q = x₁`.  `not_associated_X_zero_X_one` supplies the one geometric input, that the two inverted
  coordinates are not associate, by comparing the degree in the second variable.
  `isUnit_algebraMap_left` and `isUnit_algebraMap_right` record that the two coordinates are indeed
  invertible there.

  So `(15)--(17)` is now proved for the chart itself and not only for an abstract model of its unit
  group: a cyclic cover of `(𝔾ₘ)² × 𝔸ᴸ` whose exponent pair is nontrivial modulo `r` does not exist.
  Together with `UfdPowerDescent.lean` — every everywhere-unramified radicand is a unit times an
  `r`-th power — the whole cyclic case of the classification is formalized end to end on the real
  object.

  The single remaining input to `(4)` is the reduction of an arbitrary connected finite etale cover
  to a cyclic one, which is the abelianness of the etale fundamental group.

## Log

- 2026-08-02 — **The group theory of `(4)` is already in mathlib; the card's remaining work is
  purely geometric.**  `formal/GaloisForLFunctions/HTGeometry/CriticalMonodromyJordan.lean`, wired
  into the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  monodromy_eq_top_of_isPreprimitive_of_isSwap :
    a primitive group of permutations of the occupation states containing a transposition is S_D
  isCoatom_stabilizer_of_full_monodromy :
    and then a point stabiliser is maximal
  ```

  The first is a direct application of `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`
  in `Mathlib/GroupTheory/GroupAction/Jordan.lean` — Jordan's theorem, already formalised.  So `(4)`
  needs nothing group-theoretic from this project: the two inputs it still needs are exactly the
  geometric ones the proof section names, namely that the monodromy action on the `D` critical states
  is **primitive**, and that a meridian around the smooth generic point of the ramification divisor
  acts as **one transposition** rather than a product of several.

  Recorded so that no session re-derives Jordan.  Note also that the fibre's index type now carries
  a `DecidableEq` instance, which `IsSwap` needs and which does not follow by unification because
  `criticalHorizonOccupationStates` is a plain `def`.

- 2026-08-02 — **`(4)` does not need the irreducibility of the ramification divisor.**
  A structural observation about this card's own proof, plus the numerical form of the conclusion.

  `card_monodromy_of_isPreprimitive_of_isSwap` in
  `formal/GaloisForLFunctions/HTGeometry/CriticalMonodromyJordan.lean` (axioms
  `[propext, Classical.choice, Quot.sound]`) gives `Nat.card G = (C(L,m))!` from primitivity and one
  transposition — "full symmetric monodromy" as a number.

  The point is what the hypotheses are.  Jordan's theorem needs **one** transposition in the group;
  it does not need the ramification divisor to be irreducible, nor the monodromy to be generated by
  the conjugates of a single meridian.  The proof section above routes `(4)` through the
  irreducibility and reducedness of the rectangular Schur divisor, and irreducibility is precisely
  the input the parent bridge card `projective-horizon-irreducible-simple-ramification` cannot
  formalise, because Schur-polynomial irreducibility (Dvornicich--Zannier) has no mathlib
  counterpart.

  So `(4)` can be decoupled from that obstruction: it suffices to exhibit **one** point of the
  ramification locus at which the differential has corank one and the Jacobian vanishes to order one,
  giving one transposition, together with primitivity of the monodromy action.  Irreducibility
  remains needed for the card's *other* assertion — that the ramification divisor maps generically
  one-to-one to the branch divisor — but not for the monodromy group.

## Corpus audit — the two Lean-statable inputs that remain for `(4)`

An audit of the tree against this card's `(4)` finds the whole deduction already formal except for
two hypotheses, both of which are ordinary Lean statements about objects the corpus already defines.

Formal and unconditional (all `[propext, Classical.choice, Quot.sound]`):

```text
OccupationSubsetPrimitivity.lean
    criticalOccupationRootAction                    root permutations on the m-subset labels
    criticalOccupationRootAction_isPreprimitive     primitive when m ≠ n
    criticalMonodromy_isPreprimitive_of_rootAction_le
    criticalMonodromy_eq_top_of_rootAction_of_isSwap
        root action ≤ monodromy  +  one transposition  ⟹  monodromy = S_D      (m ≠ n)
OccupationSubsetJohnson.criticalMonodromy_eq_top_of_rootAction_of_adjacentSwap
CriticalMonodromyJordan.lean                        Jordan's theorem, wrapped
CriticalSchurInertiaAction.lean
    criticalSchurInertiaAction_range_le_monodromy   Schur inertia ⊆ monodromy
    exists_criticalGeometricMonodromy_isSwap_of_simple_nontrivial_inertia
CriticalSchurCollisionInertia.exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two
TranspositionTransitive.eq_top_of_meridian_isSwap_of_orbit_eq_univ
```

What is **not** yet a theorem, and is exactly what `(4)` still consumes:

1. `criticalOccupationRootAction K m n` has range inside `criticalGeometricMonodromy K m n` — that
   permuting the `L` roots of the pure critical fibre is realized by geometric monodromy.  A grep of
   the tree finds no statement of this; the corpus has the analogous inclusion only for the Schur
   *inertia* subgroup (`criticalSchurInertiaAction_range_le_monodromy`).
2. `Nontrivial (criticalSchurInertiaGroup K hm hn)` together with
   `∀ g, criticalSchurInertiaAction g = 1 ∨ (criticalSchurInertiaAction g).IsSwap` — simple
   nontrivial inertia at the Schur collision.  This is the "one meridian is one transposition"
   input, and `CriticalSchurCollisionInertia` already reduces it to a collision support of
   cardinality at most two.

With 1 and 2, `criticalMonodromy_eq_top_of_rootAction_of_isSwap` gives `(4)` for `m ≠ n`
unconditionally; the balanced case `m = n` still needs the geometric no-hidden-block argument, since
complement pairs are a genuine block system for the abstract `m`-subset action.

## Lean progress — the Schur input is now a *degree* statement, not a description

The transposition criterion consumed
`(collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard ≤ 2`, a statement
about *which* sheets meet.  That is now a consequence of a pure count.

```text
HTGeometry/CollisionSupportCounting.lean            (wired, axiom-clean)
    collisionSupport_ncard_le_two_of_card_le_card_image
        card α ≤ card (image r) + 1  ⟹  (collisionSupport r).ncard ≤ 2
    collisionSupport_ncard_le_two_of_natCard_le_ncard_range
        the same with cardinals, so no decidability data is needed at the use site

HTGeometry/CriticalSchurCollisionDegree.lean        (wired, axiom-clean)
    exists_criticalGeometricMonodromy_isSwap_of_reducedFibre_degree
        Nat.card (sheets) ≤ (range of the Schur reduction).ncard + 1
          + nontrivial actual Schur inertia
        ⟹  a literal transposition in criticalGeometricMonodromy
```

The counting is exact and needs nothing about the map: writing the source as the disjoint union of
the fibres, `Σ_{b ∈ image}(|fibre b| − 1) = card α − card(image r) ≤ 1`, and every colliding fibre
contributes at least `1` to that sum, so at most one fibre collides and it has exactly two elements.

What this changes for the card: step 3's conclusion no longer has to be delivered as "the two
merging sheets are exactly such-and-such".  It suffices to deliver

```text
the Schur reduction of the D sheets loses at most one point,
```

which is the divisor-theoretic content of "the Jacobian determinant is a uniformizer"
(`irreducible_criticalSchurJacobianDetElement`) — namely `Σ_w (e_w − 1) = v(𝔡) = 1` at the Schur
place, with `f_w = 1` because the residue fields are algebraically closed.  The corpus already has
irreducibility, reducedness (`orderAt_criticalSchurPrimeDivisor_ramificationPolynomial`) and generic
corank one (`finrank_ker_criticalSchurGenericMatrix_eq_one`); the missing link is the
different/Jacobian-ideal identification and the tame formula `v(𝔡) = Σ(e_w − 1)`.

Nothing here touches step 4 (the no-hidden-block argument), whose Kummer input remains as recorded.

## Lean progress — step 3's algebraic core, extracted

Step 3's contradiction (equations (9)-(13)) is pure polynomial algebra over a domain, and it is now
a theorem.  `HTGeometry/TrailingDegreeSyzygy.lean` (wired, axiom-clean):

```
not_X_pow_dvd_mul_of_trailing
    f != 0,  deg f < m,  g.coeff n != 0   ==>   not (X^(m+n) | f * g)

eq_zero_of_X_pow_dvd_mul
    the contrapositive: X^(m+n) | f g  and  g.coeff n != 0  and  deg f < m   ==>   f = 0

eq_of_low_difference
    the same phrased on a difference of two states

exists_cofactor_of_syzygy
    IsCoprime U V,  U != 0,  D V + E U = 0   ==>   exists C,  D = C U  and  E = -(C V)

eq_zero_of_tangent_syzygy
    U != 0,  D V + E U = 0,  deg D < m,  T.coeff n != 0,  X^(m+n) | D T
      ==>   D = 0  and  E = 0
```

`eq_zero_of_tangent_syzygy` is exactly the card's (9)-(13): the tangent syzygy `D0 V + E0 U = 0`,
the low degrees `deg D0 < m` and `deg E0 < n`, the marked-tail nonvanishing `[t^n](Y+Y') = 2 q_n != 0`,
and the compatibility `C U (Y+Y') = 0 mod t^L` together force `D0 = E0 = 0`.  The mechanism is the
multiplicativity of trailing degree: the trailing degree of `D0` is at most its degree, hence below
`m`, and the trailing degree of the marked tail is at most `n`, so the product has a nonzero
coefficient strictly below `m + n = L`.  Note that Euclid's lemma is *not* needed for the
conclusion — `D0` is already the low object — but it is recorded because the card's narrative uses
it to identify the cofactor.

What this leaves for step 3 in the corpus's own language is the *bridge*: producing the syzygy and
the marked-tail nonvanishing from `criticalFibre` data at the generic Schur fold, so that
`eq_zero_of_tangent_syzygy` can be applied to two geometric sheets over the same branch value.  With
that bridge, `collisionSupport_ncard_le_two_of_natCard_le_ncard_range` and
`exists_criticalGeometricMonodromy_isSwap_of_reducedFibre_degree` convert the conclusion into the
literal transposition step (4) consumes.

Caution recorded for the next session: the naive route "the reduced target `1 + U V` has one double
root, so the residue fibre loses one point" is **wrong**.  A degree-`L` target with one double root
loses `binom(L-2, m-1)` fibre points, not one, so the generic discriminant point of the *ambient*
family has inertia a product of that many disjoint transpositions.  The single transposition is
special to the Schur fold and must come from the card's syzygy argument, not from a root count.

## Step 3 is now a theorem

`criticalState_eq_of_shared_tangent` in `HTGeometry/TrailingDegreeSyzygy.lean` (wired, axiom-clean)
is the card's step 3 in full:

```
criticalState_eq_of_shared_tangent
    U != 0,  V != 0,  IsCoprime U V,
    deg U < m,  deg V < n,  deg (P'-P) < m,  deg (Q'-Q) < n,
    X^(m+n) | (P Q - 1),        X^(m+n) | (P' Q' - 1),          -- the two states
    X^(m+n) | (U Q + P V),      X^(m+n) | (U Q' + P' V),        -- the shared vertical tangent
    (P + P').coeff m != 0                                        -- the marked jet tail
  ==>  P' = P  and  Q' = Q
```

The proof is the card's (9)-(13) verbatim:

```
syzygy_of_shared_tangent   subtracting the two tangent equations leaves a polynomial of degree
                           below the horizon that the horizon divides, hence  (P'-P) V + (Q'-Q) U = 0
exists_cofactor_of_syzygy  Euclid:  P'-P = C U ,  Q'-Q = -(C V)
                           then  (Q'-Q)(P+P') = [(P'Q'-1) - (PQ-1)] - C (U Q + P V)  identically,
                           so the horizon divides the left side
eq_zero_of_X_pow_dvd_mul   trailing degree:  deg (Q'-Q) < n  and  (P+P').coeff m != 0
                           force  Q' = Q ;  the syzygy and  V != 0  then force  P' = P
```

Note the identity used in the middle step is *not* a ring identity in the free variables — it holds
only after substituting `P' = C U + P` and `Q' = -(C V) + Q`, which is what makes the cofactor
extraction essential rather than cosmetic.

### What step 3 still needs, in the corpus's own language

The theorem is stated for bare polynomials; the bridge to `criticalGeometricSheet` must supply, at
the generic Schur fold:

1. the shared vertical tangent `(U, V)` — this is the card's part 2 (the conormal pairing (8) is
   perfect, so the projective conormal line determines the projective tangent pair);
2. `U(0) != 0` and `V(0) != 0` — the card's cofactor argument (the relevant `(m-1) x (m-1)` Toeplitz
   cofactor is a nonzero Schur polynomial and cannot be divisible by the larger irreducible
   determinant), and then the degree-zero part of (6) for `V`;
3. `IsCoprime U V` — from 2 plus generic corank one;
4. the marked tail `(P + P').coeff m != 0` — the common marked tail of the two states.

Items 2 and 3 rest on `irreducible_criticalSchurJacobianDetElement` and
`finrank_ker_criticalSchurGenericMatrix_eq_one`, both already formal.

## Step 2 is now a theorem too

The perfectness of the conormal pairing (8) is `eq_zero_of_conormal_vanishing`, in the same module:

```
eq_zero_of_conormal_vanishing
    deg U < m,  deg V < n,
    for every dP with X^m | dP and every dQ with X^n | dQ,
        (U dQ - dP V).coeff (m + n - 1) = 0
  ==>  U = 0  and  V = 0
```

The proof is the card's own reason: taking `dQ = t^(n + (m-1-k))` and `dP = 0` extracts
`U.coeff k`, and taking `dP = t^(m + (n-1-k))` and `dQ = 0` extracts `V.coeff k`.  The pairing is
therefore nondegenerate on low pairs, so the conormal functional determines `(U, V)` — which is
exactly what step 3 consumes when it says the two states can be scaled to the same tangent pair.

With steps 2 and 3 both theorems, the remaining content of `(3)` is the *identification*: exhibiting
the corpus's two geometric sheets over a generic Schur branch value as a pair `(P, Q)`, `(P', Q')`
with a common vertical tangent, a nonvanishing marked jet tail, and `U(0), V(0) != 0`.

## Step 2 upgraded: the conormal line pins the tangent pair, PROVED

`HTGeometry/ConormalTangentDetermination.lean` (wired, axiom-clean).

`eq_zero_of_conormal_vanishing` said only that the zero functional forces `(U,V) = (0,0)`.  By
linearity that upgrades to determination, which is the form step 3 consumes:

```
exists_conormal_ne_zero
    a nonzero low pair is seen by some jet (the contrapositive of nondegeneracy)

conormal_determines_tangent
    two low pairs inducing the SAME functional coincide

conormal_determines_tangent_smul
    a low pair whose functional is c times another's is C c times that pair
```

The scalar form is the one the geometry actually supplies.  What the conormal geometry gives is a
*line*, not a vector, so the tangent pair is pinned only up to scale; the third theorem says that
this is the only remaining freedom.  Consequently the two states over a common generic branch value
can be rescaled to literally the same `(U, V)` — exactly the shared-tangent hypothesis of
`criticalState_eq_of_shared_tangent`.

A note on hypotheses: none of the three needs `IsDomain`.  The pairing argument is pure coefficient
extraction, so it holds over any commutative ring; only the trailing-degree half of step 3 needs a
domain.  This matters because it means the conormal half of the bridge survives base change to the
non-reduced jet rings the horizon lives over.

What still separates this from the corpus's `criticalGeometricSheet` objects is unchanged and is
recorded above: items 2 and 3 of the bridge (`U(0) != 0`, `V(0) != 0`, and coprimality from generic
corank one), which rest on `irreducible_criticalSchurJacobianDetElement` and
`finrank_ker_criticalSchurGenericMatrix_eq_one`.  Those are Schur-fold statements, not conormal
ones, and are the next brick.

## Bridge item 2 is now a theorem: the generic Schur kernel has a nonvanishing leading coordinate

`HTGeometry/CorankOneKernelSupport.lean` (general) and
`HTGeometry/CriticalSchurKernelLeadingCoefficient.lean` (at the Schur fold), both wired and
axiom-clean.

The general statement is the linear algebra the card was implicitly using:

```
mulVec_adjugate_col                     det M = 0  =>  every column of adj M is a kernel vector
ker_proportional_of_finrank_one         a corank-one kernel is spanned by any nonzero element
ker_coord_ne_zero_of_adjugate_ne_zero   corank one + adj M i j != 0
                                            =>  EVERY nonzero kernel vector has v i != 0
ker_coord_ne_zero_iff                   the SUPPORT of a corank-one kernel is independent of
                                            the vector
```

The mechanism: `M · adj M = (det M)·1 = 0` puts every adjugate column in the kernel, and one
dimension leaves no room for anything else, so a single surviving cofactor certifies a coordinate
for *all* kernel vectors at once — not merely for some distinguished one.  That "for all" is what
the card needs, because the tangent pair produced by the geometry is only known up to scale.

At the Schur fold this instantiates against the two facts already formal:

```
criticalSchurGeneric_ker_coord_zero_ne_zero
    every nonzero kernel vector of criticalSchurGenericMatrix has v 0 != 0
```

from `finrank_ker_criticalSchurGenericMatrix_eq_one` and
`criticalSchurGenericMatrix_cornerCofactor_ne_zero`.  The link between the corpus's cofactor —
stated as the determinant of the submatrix deleting the last row and first column — and the adjugate
entry at `(0, last)` is mathlib's `adjugate_fin_succ_eq_det_submatrix`, whose sign `(-1)^(last+0)` is
a unit and so does not affect vanishing; `Fin.succAbove_zero` matches `Fin.succ` to
`(0 : Fin (m'+1)).succAbove`.

That closes bridge item 2 on the `U` side.  What remains of the bridge is item 2's `V` side (the
degree-zero part of (6)) and item 3 (`IsCoprime U V` from corank one), plus the identification of
the kernel vector with the coefficient vector of `U`.

## Bridge item 3 is now a theorem: coprimality follows from generic corank one

`HTGeometry/PolynomialPairCoprimality.lean` (wired, axiom-clean).

```
isUnit_of_dvd_pair_of_finrank_one
    S a K-subspace of K[X] x K[X] with finrank K S = 1,
    (U,W) in S,  (U',W') in S,  U = g U',  U != 0     =>   IsUnit g

isCoprime_of_finrank_one
    the same S,  (U,W) in S,  U != 0,
    and: dividing both entries by any common factor stays in S
                                                      =>   IsCoprime U W
```

This is exactly the card's argument, stripped of everything particular to the Schur fold.  A line
has no room for two independent points, so the quotient pair `(U/g, W/g)` — which the hypothesis
puts back into the solution space — must be a scalar multiple `c` of `(U, W)`.  Comparing first
components gives `U = g · C c · U`, and `K[X]` is a domain with `U != 0`, so `g · C c = 1`.  Note
that only the *first* component is used: the second divisibility is not needed for the unit
conclusion, so the statement is recorded in that stronger form.

The passage from "every common divisor is a unit" to `IsCoprime` is `EuclideanDomain.gcd_isUnit_iff`
applied to `gcd U W`, whose two divisibilities feed the hypothesis directly.

With bridge item 2's `U` side (`CriticalSchurKernelLeadingCoefficient`) and item 3 now formal, what
remains of the bridge is item 2's `V` side — the degree-zero part of `(6)` — and the identification
of the corank-one kernel vector with the coefficient vector of `U`.

## Bridge item 2's `V` side is now a theorem

`HTGeometry/SyzygyConstantTerm.lean` (wired, axiom-clean).

```
syzygy_coeff_zero
    t^L | (U Y + X V) ,  L >= 1     =>   U(0) Y(0) + X(0) V(0) = 0

syzygy_coeff_zero_ne_zero
    the same, over a domain, with  U(0) != 0  and  Y(0) != 0   =>   V(0) != 0
```

This is the card's "the degree-zero part of `(6)` then also makes `V(0)` nonzero", with no
hypothesis on `X` at all: if `V(0)` vanished, the second product would drop out of the degree-zero
identity and the first would have to vanish too, which a domain forbids once `U(0)` and `Y(0)` are
nonzero.  The divisibility hypothesis is used only through `Polynomial.X_pow_dvd_iff` at index `0`.

Bridge status after this and the previous two sections:

```
item 2, U side   CriticalSchurKernelLeadingCoefficient        DONE
item 2, V side   SyzygyConstantTerm                            DONE  (this section)
item 3           PolynomialPairCoprimality                     DONE
```

What remains of the bridge is the identification of the corank-one kernel vector with the
coefficient vector of `U` — a statement about the corpus's own Schur matrix, not a new piece of
algebra — and, separately from the bridge, the two `(4)` inputs recorded above: the inclusion of the
root action in the geometric monodromy, and nontrivial simple inertia at the Schur collision.

## Correction — audit item 1 is not an independent input

The "Corpus audit" section above lists as input 1

> `criticalOccupationRootAction K m n` has range inside `criticalGeometricMonodromy K m n`

and treats it as an ordinary geometric statement waiting to be proved.  It is not: on the locus
where it is visible it is **false**, and everywhere else it is equivalent to `(4)` itself.

The reason is a forced identity.  A state has the subset labelling only when the two factors have
their exact degrees, i.e. when the raw tail is `x_m ≠ 0, x_(m+1) = … = x_(L-1) = 0` **and** the
reciprocal tail is `y_n ≠ 0, y_(n+1) = … = y_(L-1) = 0`.  Then `deg X = m`, `deg Y = n`, so `X Y` is
of degree exactly `L`, and `X Y ≡ 1 mod t^L` leaves only the top coefficient free:

```text
X Y = 1 + c t^L,        c = x_m y_n.
```

So the pure locus is two-dimensional and its fibres are the `m`-subsets of the roots of `1 + c t^L`
— *never* of a general degree-`L` polynomial.  The roots are `ζ^j ρ`, `ρ^L = -1/c`, so continuation
in the only free parameter `c` realizes exactly the cyclic shift of the `L` roots.  The monodromy
of the pure sub-family is therefore `Z/L`, not `S_L`, and the subgroup of `Perm(states)` it produces
is the image of one `L`-cycle acting on `m`-subsets — which is not even transitive on them (for
`L = 4, m = 2` it has orbits of sizes `4` and `2`).

Off the pure locus there is no subset labelling to permute, so the only way `criticalOccupationRootAction`
can land in `criticalGeometricMonodromy` is for the monodromy to be all of `S_D` already.  Hence
input 1 cannot be used to prove `(4)`; it is a consequence of it.

**What this means for the card.**  `criticalMonodromy_eq_top_of_rootAction_of_isSwap` is still a
correct theorem, but its `hroot` hypothesis has no independent proof, so the route
"root action + one transposition" is closed.  The only surviving route to `(4)` is step 4 as
originally written: transitivity (already formal), one transposition (input 2, still open but
reduced to a degree count), and **primitivity**, which by the Galois correspondence is exactly

```text
no field strictly between  O(m,n;L-1)  and  J_(L-1).
```

Step 4 proves that by classifying the finite étale covers of the chart `(𝔾ₘ)² × 𝔸^(L-2)`.  Every
downstream piece of that classification is now formal — `UfdPowerDescent`,
`LocalizationTwoPrimeUnits`, `TorusKummerExponents` — and the one missing step is the reduction of
an arbitrary connected finite étale cover of that chart to a cyclic one.  That is
`π₁^ét((𝔾ₘ)² × 𝔸^(L-2)) = Ẑ(1)²` in characteristic zero, i.e. simple connectedness of affine space,
whose only known proofs are Riemann existence (over `ℂ`) plus Lefschetz descent, or a
Bertini/Riemann–Hurwitz reduction to curves.  mathlib has no étale fundamental group, no Bertini,
and no Riemann–Hurwitz, so this is an infrastructure gap of a different order from the rest of the
card, not a missing lemma.

Restricting the intermediate cover to a general line inside `{p_m = q_n = 1} ≅ 𝔸^(L-2)` reduces the
statement to "a connected finite étale cover of `𝔸¹` in characteristic zero is trivial", which
Riemann–Hurwitz proves in three lines (`2g-2 = -2D + Σ(e-1) ≤ -D-1` forces `D ≤ 1`).  The step that
is *not* elementary is the Bertini/Lefschetz input that the restriction to a general line stays
connected.  That is the precise shape of the remaining gap, and it is the same gap for both
projective-horizon cards, since `projective-horizon-one-step-postcritical-rigidity` consumes
primitivity through `(7)`.

## PROGRAMME (2026-08-18) — an elementary route to `(4)` that never uses the étale fundamental group

The obstruction recorded above ("the reduction of an arbitrary connected finite étale cover of
`(𝔾ₘ)² × 𝔸^(L-2)` to a cyclic one") is **not** needed.  The torus that acts on the whole horizon
family supplies the cyclicity for free, and the only genuinely new input becomes the algebraic simple
connectedness of affine space.  Full derivation, to be executed as a long programme.

### The torus splits the chart, algebraically

`T = 𝔾ₘ²` acts by `x_i ↦ λ μ^i x_i`, `y_j ↦ λ^(-1) μ^j y_j`; the horizon map is equivariant.  Put

```text
S   = { x_m = 1 , y_n = 1 }  ≅  𝔸^(L-2)       (slice)
c   = x_m y_n
O'  = O( c^(1/L) )                             (cyclic of degree L over O)
```

`T × S → chart` is finite of degree `L` (stabiliser `μ_L`, from `μ^L = c`), and on function fields

```text
O' = K(λ^{±}, μ^{±}, w_1, …, w_{L-2}) = O_S(λ, μ),      μ^L = c,  λ = x_m μ^(-m),
                                                        w_i = (x_i/x_m) μ^(m-i).
```

So `O'` is **purely transcendental of degree 2 over the slice field `O_S = K(w)`**, and by
equivariance the cover over `T × S` is the pullback of the cover over `S`:

```text
J' := J·O' = J_S(λ, μ),      Gal(J'/O') ≅ Gal(J_S/O_S)          (free-parameter base change,
                                                                  already formal in this tree)
```

### The endgame

Let `H` be the normal closure of one Schur meridian, `M` the fixed field of the stabiliser of the
block of a chosen sheet (`M` = the "block cover", `[M:O] = k = D/b`).  Then

```text
E1  branch locus of J/O inside the chart = the Schur divisor          (only open geometry input)
E2  the Schur meridian is one transposition                            (already reduced to a count)
E3  ⟹ M/O is unramified at EVERY height-one prime of the chart ring R
E4  every prime divisor Z of S gives the T-invariant prime divisor T·Z of the chart, so
    M_S/O_S is unramified at every height-one prime of K[w_1,…,w_(L-2)]
E5  (SC_k)  𝔸^k is algebraically simply connected in characteristic zero
        ⟹  M_S = O_S  ⟹  M·O' = O'  ⟹  M ⊆ O'
E6  M is then an intermediate field of the CYCLIC extension O'/O, so M = O(c^(1/k)) with k | L;
    but c^(1/k) ∈ J and the raw coordinate divisor gives v_m(c) = v_m(x_m y_n) = 1,
    so k · v_m(c^(1/k)) = 1, hence k = 1.
E7  ⟹ the block system is trivial, H is transitive, H is generated by transpositions, so H = S_D,
    hence `criticalGeometricMonodromy = ⊤`, which is `(4)`.
```

`E6` needs no UFD descent and no cover classification: it is one valuation.  `E1`, `E2` are the
geometry the card already isolates.  **The single new piece of mathematics is `E5`.**

### E5, and how it is elementary

```text
SC_1(ℂ)   f ∈ ℂ[s][T] monic in T with disc_T f ∈ ℂ^×  ⟹  f splits into monic linear factors
          in ℂ[s][T].
              {(s,T) : f = 0} → ℂ is a covering map (simple roots + holomorphic IFT + properness);
              ℂ is simply connected, so a global continuous section exists; it is holomorphic and of
              polynomial growth (root bound for a monic polynomial), hence a polynomial; divide and
              induct on the degree.
SC_1(K)   transfer to any algebraically closed K of characteristic zero: the coefficients generate a
          countable algebraically closed subfield, which embeds into ℂ.
SC_k      induction on k.  With 𝔽 = K(u_1,…,u_(k-1)), a finite extension of 𝔽(u_k) unramified over
          𝔽[u_k] becomes split over the algebraic closure by SC_1, hence is a constant extension
          𝔽'(u_k); the Gauss valuation transports unramifiedness of 𝔽'/𝔽 to every height-one prime
          of K[u_1,…,u_(k-1)]; induct.
```

Every step is field/valuation theory plus one-variable complex analysis.  No schemes, no purity, no
Bertini, no Riemann–Hurwitz, no étale fundamental group.

Corpus assets that already exist for `SC_1(ℂ)`: `U0.HolomorphicIFT.holo_implicit`,
`Bottcher.ProperLocalHomeoCovering.isCoveringMap_of_isProperMap_of_isLocalHomeomorph`,
`Bottcher.EntirePolyGrowth.exists_polynomial_of_entire_polyGrowth`,
mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts`, and the pattern of
`HTGeometry.SpectralPathCovering` (the same covering built over the unit interval).

## Lean progress — `SC_1` is PROVED, unconditionally, over every algebraically closed field of characteristic zero

Four new modules, all wired into `HTGeometry` and all axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

```text
HTGeometry/BivariateRootCovering.lean
    biEval, biFibre, BiRootLocus, biRootProj
    isLocalHomeomorph_biRootProj        the implicit-function chart on the root locus
    isProperMap_biRootProj              uniform Cauchy bound on compacta
    isCoveringMap_biRootProj            ** the root locus of a monic family with separable fibres
                                           is a covering space of the parameter plane **

HTGeometry/ComplexAffineLineSimplyConnected.lean
    exists_continuous_biRoot            global section (ℂ simply connected + mathlib's lifting)
    analyticAt_of_continuous_biRoot     the section is analytic (local uniqueness in the chart)
    exists_polynomial_biRoot            it has polynomial growth, hence IS a polynomial
    exists_monic_linear_factor
    exists_multiset_prod_of_forall_separable   ** SC_1 over ℂ **

HTGeometry/CountableFieldComplexEmbedding.lean
    infinite_of_isTranscendenceBasis_complex
    exists_algebraicIndependent_nat_complex
    nonempty_ringHom_complex_of_countable      ** every countable characteristic-zero field
                                                  embeds into ℂ **

HTGeometry/BivariateSeparableResultant.lean
    biResultant, separable_iff_resultant_ne_zero, biResultant_eval
    exists_biResultant_eq_C             over an algebraically closed field, separable fibres
                                        ⟺ the fibre resultant is a nonzero CONSTANT
    forall_separable_of_biResultant_eq_C        the converse over any field
    biResultant_map                     the fibre resultant commutes with any coefficient map

HTGeometry/AffineLineSimplyConnected.lean
    exists_map_eq_of_eval_mem_range     Lagrange descent
    exists_isRoot_of_countable          the countable case, through ℂ
    exists_isRoot_of_forall_separable
    exists_multiset_prod_of_forall_separable_algClosed
        ** SC_1 : over ANY algebraically closed field of characteristic zero, a monic
           f ∈ K[X][X] with every fibre separable splits into monic linear factors **
```

The two devices that make the transfer work and are worth remembering: (i) "every fibre separable"
is **equivalent to the fibre resultant being a nonzero constant**, and that form is preserved by
*any* ring homomorphism, so the hypothesis transports to ℂ for free; (ii) the complex root branch
descends again by **Lagrange interpolation** — it maps the image field into itself because that
field is algebraically closed and the branch value is a root of a polynomial over it.

### Next: `SC_k` by an elementary induction (no Bertini, no constant-extension theory)

The multivariable case does **not** need the constant-field-extension/Gauss-valuation argument
sketched in the programme.  With `B` a characteristic-zero domain and `A = B[w]`:

```text
f ∈ A[X] monic, res(f, ∂f) a unit
  → over the algebraic closure 𝔽̄ of Frac(B), SC_1 splits f = ∏ (X - g_i), g_i ∈ 𝔽̄[w]
  → disc(f) = ∏_{i<j}(g_i-g_j)^2 is a unit, so every g_i - g_j is a unit of 𝔽̄[w], i.e. a CONSTANT
  → hence g_i = h + a_i with h = -(1/d)·(coefficient of X^{d-1}) ∈ A and a_i ∈ 𝔽̄
  → so F(X) := f(X + h) has all coefficients constant in w, i.e. F ∈ B[X], monic, same resultant
  → induction on the number of variables gives F = ∏ (X - b_i) with b_i ∈ B
  → f(X) = F(X - h) = ∏ (X - h - b_i) splits over A.
```

Base case `B = K`: a monic polynomial over an algebraically closed field splits.  The whole
induction is elementary once `SC_1` is available.

## Lean progress — `SC_k` in monogenic form is PROVED

`HTGeometry/AffineSpaceSimplyConnected.lean` (wired, axiom-clean):

```text
HasEtaleSplitting B          every monic f ∈ B[X] with IsUnit (resultant f (derivative f))
                             splits into monic linear factors
hasEtaleSplitting_of_isAlgClosed      the base case
exists_constant_shift        ** over an algebraically closed field of characteristic zero, all
                                roots of a monic two-variable polynomial with separable fibres are
                                one fixed polynomial plus constants **
hasEtaleSplitting_polynomial ** the property passes from B to B[X] **
hasEtaleSplitting_of_ringEquiv
hasEtaleSplitting_mvPolynomial
    ** SC_k : over an algebraically closed field of characteristic zero, a monic polynomial over
       a polynomial ring in k variables whose resultant against its derivative is a UNIT splits
       into monic linear factors **
```

The mechanism of `exists_constant_shift` is worth recording: separability of *every* fibre forces
each difference of two roots to have no zero, hence (algebraically closed base) to be a constant;
so the roots are `h + a_i` with `h = -(1/d)·(subleading coefficient)` and `a_i` constants, and
translating by `h` produces a polynomial with one fewer variable.

### The remaining gap, stated exactly

`SC_k` as proved is the **monogenic** form: it needs the cover presented as `A[X]/(p)` with
`res(p, p')` a *unit*.  The block cover of the endgame is étale over `A = K[w₁,…,w_{L-2}]`, but a
monogenic model with unit resultant is exactly the statement that its integral closure is generated
by one element, which does not follow formally.  So the endgame needs the **general** form:

```text
SCE_k :  B a finite free algebra of rank n over MvPolynomial (Fin k) K, K algebraically closed of
         characteristic zero, with Algebra.discr a unit  ⟹  B ≅ A^n  (equivalently, a connected
         such B has rank 1).
```

Note what does *not* work, so no session repeats it: taking a generic primitive element
`θ = Σ t_i b_i` (even after adjoining the `t_i` as new variables) makes the discriminant a nonzero
polynomial but never a unit — its vanishing locus is a hyperplane arrangement — because for a
*split* cover the good generators are precisely the locally constant ones.  Monogenicity of an
étale algebra over a polynomial ring is therefore equivalent to, not weaker than, what is being
proved; a genuinely different argument is required for `SCE_1`, and the induction of
`hasEtaleSplitting_polynomial` then carries it to all `k`.

## Why the monogenic form cannot be patched, and the exact shape of `SCE`

A structural remark that closes off several tempting shortcuts.  Suppose a connected finite étale
cover of `𝔸^k` (algebraically closed base, characteristic zero) had a monogenic model `A[β]` with
`res` a unit.  Then every two conjugates of `β` differ by a nowhere-vanishing function, i.e. by a
nonzero constant, so by `exists_constant_shift` all conjugates are `h + a_i` with `a_i` constants,
whence the cover is a *constant* extension and therefore trivial.  So:

```text
a nontrivial connected finite étale cover of 𝔸^k admits NO monogenic model with unit resultant.
```

Consequently `hasEtaleSplitting_mvPolynomial` can never be applied to an abstract étale cover; it can
only be applied when a monogenic model is exhibited.  In particular the block cover of the endgame —
whose conjugate block-invariants (sums, elementary symmetric functions, `∏(u - σ x₀)` for a new
variable `u`, or any single element) always collide on a divisor unless the cover is split — cannot
be fed to it.  The endgame needs

```text
SCE_k :  A = MvPolynomial (Fin k) K, K algebraically closed of characteristic zero,
         B a finite free A-algebra of rank n with `Algebra.discr` a unit
           ⟹  B ≅ A^n   (equivalently: a connected such B has rank one).
```

### Build plan for `SCE`

```text
SCE_1(ℂ)   B free étale of rank n over ℂ[w].
           (a) LOCAL MONOGENICITY: for every s, B ⊗ A_{𝔪_s} = A_{𝔪_s}[θ] by Nakayama, since
               B/𝔪_s B ≅ ℂ^n is monogenic over ℂ; hence B is monogenic with unit resultant on a
               Zariski neighbourhood of s.  For a fixed primitive θ the bad locus is FINITE, so
               finitely many charts suffice.
           (b) The space E of ℂ-algebra homomorphisms B → ℂ, topologised inside ℂ × ℂⁿ by the
               values on an A-basis, projects to ℂ with exactly n points in each fibre, and on each
               chart it is the `BiRootLocus` of the local monogenic model — already proved to be a
               covering space in `BivariateRootCovering`.
           (c) ℂ is simply connected, so E → ℂ has a section; the section is analytic and of
               polynomial growth on each basis element (integrality), hence an A-algebra map
               B → A.  Split it off and induct on the rank.
SCE_1(K)   transfer to any algebraically closed characteristic-zero field, exactly as in
           `AffineLineSimplyConnected` (the discriminant being a unit is preserved by any ring map).
SCE_k      induction on k by constant-field descent: `B ⊗ 𝔽̄[w]` splits by `SCE_1`; an étale
           `𝔽[w]`-algebra split by `𝔽̄` is constant; the constant algebra is étale over the smaller
           polynomial ring by the Gauss valuation; induct.
```

Note that `exists_constant_shift`'s trick does **not** transfer to `SCE_k` directly, because for a
non-monogenic cover the sections over `𝔽̄[w]` need not differ by constants; the descent route above
is the replacement.

## Lean progress — the local input for `SCE` is in

`HTGeometry/LocalNakayamaMonogenic.lean` (wired, axiom-clean):

```text
adjoin_eq_top_of_le_maximalIdeal_smul
adjoin_eq_top_of_forall_sub_mem       ** a finite algebra over a LOCAL ring is generated by any
                                         element whose residues generate the fibre **
exists_adjoin_eq_top_of_forall_sub_mem
```

mathlib's `IsLocalRing.exists_adjoin_eq_top` requires the upper ring to be local too, which is
exactly what fails here (the fibre is a product of `n` copies of the residue field), so the Nakayama
argument is redone without that hypothesis.

### The `SCE_1(ℂ)` construction, refined

The local monogenicity can be turned into a *global polynomial* datum, which is the simplification
that makes the covering-space step tractable:

```text
for each s ∈ ℂ there is θ_s ∈ B with
    A_{𝔪_s}[θ_s] = B_{𝔪_s}                        (Nakayama; the fibre is ℂⁿ, hence monogenic)
    p_s := charpoly of θ_s on the free module B   ∈ A[X], monic of degree n
    disc(p_s) = (index)² · disc(B/A),  so disc(p_s)(s) ≠ 0
hence on the Zariski-open U_s = {disc(p_s) ≠ 0} (complement finite):
    A_{U_s}[θ_s] = B_{U_s}   and   every fibre of p_s over U_s is separable.
```

So on `U_s` the space of points is literally the `BiRootLocus` of `p_s`, already proved to be a
covering space.  Since every `s` has such a `U_s`, the space

```text
E := (B →ₐ[ℂ] ℂ)   with the topology induced from the product topology on `B → ℂ`,
π : E → ℂ,  χ ↦ χ(w)
```

is a covering map; `ℂ` is simply connected, so it has a global section; the section is analytic on
each `U_s` (it is `q(s, root)/g(s)` there) and of polynomial growth on each basis element, hence a
polynomial, so it is an `A`-algebra map `B → A`.  Splitting it off and inducting on the rank gives
`B ≅ Aⁿ`.

## Lean progress — the chart datum for `SCE_1`

`HTGeometry/AlgebraSpectrumTopology.lean` (wired, axiom-clean):

```text
AlgSpec B                    the ℂ-points of a ℂ-algebra, topologised pointwise
continuous_eval, isEmbedding_coe
proj B, continuous_proj      the projection to the parameter line, for a ℂ[X]-algebra
apply_algebraMap             a ℂ-point evaluates the polynomial ring at its projection
apply_aeval                  ** χ (aeval θ q) = biEval q (proj χ, χ θ) **
toPlane θ, continuous_toPlane
toPlane_mem_biRootLocus      ** the chart lands on the root locus of any monic relation for θ **
toPlane_injOn                ** where θ generates, the chart is injective **
```

Together with `LocalNakayamaMonogenic` this reduces `SC_E1` to: (i) surjectivity of the chart onto
the root locus over `U` — i.e. `B_U ≅ A_U[T]/(p)` through `IsAdjoinRootMonic`; (ii) the resulting
homeomorphism transfers `IsEvenlyCovered` from `isCoveringMap_biRootProj`; (iii) the section
supplied by simple connectedness of `ℂ` is analytic and of polynomial growth, hence an `A`-algebra
map `B → A`; (iv) split it off and induct on the rank.

### Status of the whole programme

```text
SC_1 over any algebraically closed characteristic-zero field   DONE
SC_k, monogenic form                                            DONE
Nakayama local monogenicity                                     DONE
chart datum for SCE_1                                           DONE
SCE_1  (steps (i)-(iv) above)                                   IN PROGRESS
SCE_k  (constant-field descent)                                 OPEN
E1  branch locus in the chart = the Schur divisor               OPEN  (this is the discriminant
                                                                       computation, and it also
                                                                       delivers E2's degree count)
E2  Schur inertia nontrivial and simple                         OPEN
torus/slice bookkeeping and the final Kummer valuation          OPEN  (no new mathematics)
```

`HTGeometry/AlgebraSpectrumFibre.lean` (wired, axiom-clean) adds the fibrewise half:

```text
card_setOf_isRoot     a separable monic complex polynomial has exactly natDegree roots
mapsTo_eval_fibre     the value map sends the fibre of proj into the roots of the specialised
                      relation
bijOn_eval_fibre      ** and it is a BIJECTION onto them, given generation on U, separability of
                         the specialised relation, and the expected fibre cardinality **
```

Remaining for `SCE_1`: the continuity of the inverse chart (each `b` is `q_b(s,t)/g_b(s)` there, so
the inverse into `B → ℂ` is continuous and the induced topology does the rest); the transfer of
`IsEvenlyCovered`; the section from simple connectedness of `ℂ`; and the analyticity/growth step
turning the section into an `A`-algebra map `B → A`.  The hypothesis producer — from `B` free étale
over `ℂ[X]` to a `θ`, `p`, `U` with the generation property — is `LocalNakayamaMonogenic` plus
clearing one denominator for each of finitely many module generators.

`HTGeometry/AlgebraSpectrumChart.lean` (wired, axiom-clean):

```text
eval_eq_of_gen                 χ b = biEval q (toPlane θ χ) / g.eval (proj χ)
continuousOn_of_toPlane_eq     ** any set-theoretic inverse of the chart map is continuous **
```

### Exactly what is left in `SCE_1`, as Lean steps

```text
1. hypothesis producer:  B free étale over ℂ[X]  ⟹  for each s₀ a θ, its characteristic
   polynomial p (monic, degree n, in ℂ[X][X]), and U = {disc(p) ≠ 0} ∋ s₀ with
     · aeval θ p = 0                                      (Cayley–Hamilton)
     · ∀ b, ∃ q g, (∀ s ∈ U, g.eval s ≠ 0) ∧ g • b = aeval θ q
       (LocalNakayamaMonogenic at 𝔪_{s₀}, then clear one denominator per module generator)
     · ∀ s ∈ U, (biFibre p s).Separable                   (disc(p) ≠ 0 on U)
     · the fibre of proj over each s has ncard n          (the fibre algebra is ℂⁿ)
2. bijOn_eval_fibre + continuousOn_of_toPlane_eq  ⟹  toPlane θ restricts to a HOMEOMORPHISM
   proj⁻¹(U) ≃ₜ biRootProj⁻¹(U)  commuting with the two projections.
3. IsCoveringMapOn.of_isCoveringMap_restrictPreimage together with
   isCoveringMap_biRootProj  ⟹  IsEvenlyCovered (proj B) s₀, for every s₀, i.e.
   IsCoveringMap (proj B).
4. ℂ is simply connected and locally path connected, so mathlib's
   IsCoveringMap.existsUnique_continuousMap_lifts gives a global section σ : ℂ → AlgSpec B.
5. For each b, s ↦ σ(s) b is analytic (on each U it is q(s,t)/g(s) with t the analytic root
   branch) and of polynomial growth (b is integral over ℂ[X]), hence a polynomial —
   `Bottcher.exists_polynomial_of_entire_polyGrowth`, exactly as in
   ComplexAffineLineSimplyConnected.
6. b ↦ that polynomial is a ℂ[X]-algebra map B → ℂ[X]; split off the idempotent it defines and
   induct on the rank to get B ≅ ℂ[X]ⁿ.
```

**Design note for step 3, recorded before it is built.**  `isCoveringMap_biRootProj` assumes
separability of *every* fibre, but the chart only has it on `U = {disc(p) ≠ 0}`.  So step 3 needs an
"on `U`" version — `IsCoveringMapOn biRootProj U`, equivalently `IsCoveringMap` of
`U.restrictPreimage biRootProj`.  Both existing ingredients survive the restriction unchanged:
`biRootLocus_partial_ne` only uses separability *at the point in question*, and the Cauchy root
bound gives properness over any compact subset of `U`.  Add these as new declarations rather than
weakening the landed ones, which `ComplexAffineLineSimplyConnected` consumes in their global form.

**Step 3 preparation, done.**  `biRootLocus_partial_ne`, `biIFTData`, `biIFTData_apply` and
`biIFTData_mem_source` in `BivariateRootCovering.lean` now take separability *at the point of the
root locus* rather than at every parameter, which is what an "on `U`" covering statement needs;
`isLocalHomeomorph_biRootProj` and `isCoveringMap_biRootProj` keep their global hypotheses and
simply feed `hsep _`.

**A better route for step 3, recorded.**  Rather than an "on `U`" covering statement for the root
locus, apply
`Bottcher.isCoveringMap_of_isProperMap_of_isLocalHomeomorph` to `AlgSpec.proj B` itself:

* `IsLocalHomeomorph (proj B)` — at each `χ₀`, the chart `toPlane θ` is a homeomorphism of
  `proj⁻¹(U)` onto `biRootProj⁻¹(U)` (bijection from `bijOn_eval_fibre`, inverse continuous from
  `continuousOn_of_toPlane_eq`), and `biRootProj` is a local homeomorphism at each point of that
  set because `biIFTData` now only needs separability *at the point*.
* `IsProperMap (proj B)` — by **Tychonoff**, with no reference to charts at all: for compact
  `K ⊆ ℂ`, every `b ∈ B` is integral over `ℂ[X]`, so the Cauchy root bound makes `|χ b|` bounded
  uniformly over `proj⁻¹(K)`; hence `proj⁻¹(K)` embeds into a product of closed discs, and it is
  closed there because being a ring homomorphism is a pointwise-closed condition.  A closed subset
  of a compact product is compact.

This is much cheaper than restricting the root-locus covering to an open set.

`HTGeometry/AlgebraSpectrumClosed.lean` (wired, axiom-clean):

```text
AlgSpec.instT2Space
AlgSpec.isClosed_range_algSpec_coe   ** being a ℂ-algebra homomorphism is a pointwise-closed
                                        condition, so the complex-point space is closed in B → ℂ **
```

That is the harder half of the Tychonoff properness argument; what remains of it is the uniform
Cauchy bound `|χ b| ≤ C_b(K)` on `proj⁻¹(K)`, which is `Bottcher.norm_root_le_of_monic` applied to
a monic relation for `b` over `ℂ[X]` (available because `B` is finite over `ℂ[X]`, so every element
is integral).

`HTGeometry/AlgebraSpectrumProper.lean` and `HTGeometry/AlgebraSpectrumBijection.lean`
(wired, axiom-clean):

```text
AlgSpec.norm_apply_le_of_monic   the Cauchy bound at a complex point, from a monic relation
AlgSpec.isProperMap_proj         ** the projection of the complex-point space is PROPER **
                                    (Tychonoff: closed inside a product of closed discs)
AlgSpec.bijOn_toPlane            ** the chart is a BIJECTION from proj⁻¹(U) onto the part of the
                                    root locus above U **
```

So the two halves of `Bottcher.isCoveringMap_of_isProperMap_of_isLocalHomeomorph` are now in
different states: properness is **done**, and the local homeomorphism needs only the transport of
`isLocalHomeomorph_biRootProj` (which now takes separability *at a point*) through the homeomorphism
assembled from `bijOn_toPlane` + `continuousOn_of_toPlane_eq`.

### The one remaining step of the covering property, written out

The inverse chart is available concretely: with
`T := {z | z ∈ BiRootLocus p ∧ z.1 ∈ U}` and `hbij := bijOn_toPlane …`, set

```lean
Ψ : ℂ × ℂ → AlgSpec B := fun z => if h : z ∈ T then (hbij.2.2 h).choose else χ₀
```

Then `∀ z ∈ T, Ψ z ∈ proj B ⁻¹' U` and `∀ z ∈ T, toPlane θ (Ψ z) = z` hold by `choose_spec`
(unfold with `simp only [hΨ, dif_pos hz]`, not `rw`), and `ContinuousOn Ψ T` is exactly
`continuousOn_of_toPlane_eq hgen Ψ …`.  This is verified.

What is left is bookkeeping only: assemble `toPlane θ` and `Ψ` into an
`OpenPartialHomeomorph (AlgSpec B) ℂ` whose source is a neighbourhood of `χ₀` on which `proj` is
injective — take the `toPlane`-preimage of the source of the root-locus chart at `toPlane θ χ₀`
supplied by `isLocalHomeomorph_biRootProj`'s construction (which now only needs separability at
that point) — giving `IsLocalHomeomorph (proj B)`, and then

```text
Bottcher.isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (isLocalHomeomorph …) AlgSpec.isProperMap_proj   ⟹   IsCoveringMap (AlgSpec.proj B)
```

after which steps 4–6 of the plan above run exactly as in `ComplexAffineLineSimplyConnected`.

## Lean progress — the covering property of the complex-point space is PROVED

`HTGeometry/AlgebraSpectrumCovering.lean` (wired, axiom-clean), and a small refactor of
`BivariateRootCovering.lean` (`exists_chart_biRootProj`, the root-locus chart at a point where the
fibre is separable; `isLocalHomeomorph_biRootProj` is now a one-line corollary):

```text
AlgSpec.isLocalHomeomorph_proj_of_chart   the partial homeomorphism at one point, assembled from
                                          bijOn_toPlane, continuousOn_of_toPlane_eq and
                                          exists_chart_biRootProj
AlgSpec.isLocalHomeomorph_proj
AlgSpec.isCoveringMap_proj
    ** the space of complex points of a finite ℂ[X]-algebra is a COVERING SPACE of the parameter
       line, given at each point a θ, a monic relation p, and an open U with: θ generating over U,
       every fibre of p over U separable, and every fibre of proj over U of cardinality
       p.natDegree **
```

This is the hard topological core of `SCE_1`.  What is left of `SCE_1` is:

```text
(a) hypothesis producer: B free étale over ℂ[X] (every fibre split) ⟹ the chart data at each point.
    θ from LocalNakayamaMonogenic at 𝔪_s (the fibre ℂⁿ is monogenic); p := the characteristic
    polynomial of θ on the free module B, so aeval θ p = 0 by Cayley–Hamilton and p is monic of
    degree n; U := {disc p ≠ 0}, which contains s because A_{𝔪_s}[θ] = B_{𝔪_s}; generation over U
    by clearing one denominator per module generator; the fibre cardinality is n by hypothesis.
(b) the section: IsCoveringMap.existsUnique_continuousMap_lifts against the identity of ℂ.
(c) the section is an algebra map into ℂ[X]: for each b, s ↦ σ(s) b is analytic (on each U it is
    q(s,t)/g(s) with t the analytic root branch) and of polynomial growth by
    AlgSpec.norm_apply_le_of_monic, hence a polynomial —
    Bottcher.exists_polynomial_of_entire_polyGrowth.
(d) split off the resulting idempotent and induct on the rank.
```

`HTGeometry/AlgebraCharpoly.lean` (wired, axiom-clean) supplies the monic relation of step (a):

```text
algCharpoly A θ          the characteristic polynomial of multiplication by θ
algCharpoly_monic
aeval_algCharpoly        ** Cayley–Hamilton for a finite free algebra: aeval θ (algCharpoly A θ) = 0 **
```

So of step (a) only the Nakayama/denominator-clearing half is left: from
`Algebra.adjoin A_{𝔪_s} {θ} = ⊤` (`LocalNakayamaMonogenic` applied to the fibre `ℂⁿ`, which is
monogenic because `ℂ` is infinite) produce `g ∈ ℂ[X]` with `g(s) ≠ 0` and
`g • bᵢ = aeval θ qᵢ` for the finitely many module generators `bᵢ`, then take
`U := {disc(algCharpoly) ≠ 0} ∩ {g ≠ 0}`.

### Step (a) without any localization — use Cramer instead of Nakayama

`LocalNakayamaMonogenic` is not actually needed for the chart data, and neither is the localization
API.  Fix an `A`-basis `e` of `B` (`A = ℂ[X]`, `B` free of rank `n`) and, for `θ ∈ B`, let

```text
M(θ) := the matrix expressing 1, θ, …, θ^{n-1} in the basis e
g(θ) := det M(θ)  ∈ A
```

Cramer's rule `adj M · M = (det M) • 1` gives, with no hypotheses at all,

```text
g(θ) • e_i = aeval θ q_i ,      q_i := Σ_j (adj M(θ))_{ij} X^j ,
```

hence `g(θ) • b = aeval θ q_b` for every `b`, which is exactly the generation datum the chart needs
with `U ⊆ {g(θ) ≠ 0}`.  And `g(θ)(s) ≠ 0` holds as soon as `θ` has `n` distinct values on the fibre
at `s` (Vandermonde), which can be arranged because the fibre is `ℂⁿ` and `B` surjects onto it.

So step (a) is: pick `θ` whose fibre values at `s` are distinct; take
`p := algCharpoly ℂ[X] θ` (monic, degree `n`, `aeval θ p = 0` by `aeval_algCharpoly`); take
`U := {g(θ) ≠ 0} ∩ {disc p ≠ 0}`, an open set containing `s`.  Separability of the fibres of `p`
over `U` and the fibre cardinality are then immediate.  No Nakayama, no localization.

`HTGeometry/PowerMatrixCramer.lean` (wired, axiom-clean) delivers the generation datum:

```text
powerMatrix e θ                 the coordinate matrix of 1, θ, …, θ^(n-1) in a basis e
det_powerMatrix_smul_basis      Cramer: det • e i = Σ_j (adj) j i · θ^j
exists_aeval_of_det_smul        ** det (powerMatrix e θ) • b = aeval θ q for every b **
```

Combined with `AlgebraCharpoly`, step (a) of `SCE_1` is now reduced to two elementary facts about a
single parameter `s`: that some `θ ∈ B` has `n` distinct values on the fibre (the fibre is `ℂⁿ` and
`B` surjects onto it), and that then `det (powerMatrix e θ)(s) ≠ 0` (Vandermonde) and
`disc(algCharpoly θ)(s) ≠ 0`.  Take `U` to be the intersection of the two nonvanishing loci.

(The Vandermonde half of step (a) needs no new module: `Matrix.det_vandermonde_ne_zero_iff` is
exactly it — verified against this toolchain.)

## Session ledger — modules landed for this card

```text
BivariateRootCovering          ComplexAffineLineSimplyConnected   CountableFieldComplexEmbedding
BivariateSeparableResultant    AffineLineSimplyConnected          AffineSpaceSimplyConnected
LocalNakayamaMonogenic         AlgebraSpectrumTopology            AlgebraSpectrumFibre
AlgebraSpectrumChart           AlgebraSpectrumClosed              AlgebraSpectrumProper
AlgebraSpectrumBijection       AlgebraSpectrumCovering            AlgebraCharpoly
PowerMatrixCramer
```

All sixteen are wired into `GaloisForLFunctions.HTGeometry`, pass the formal lint gate, and use only
`[propext, Classical.choice, Quot.sound]`.  The two headline theorems are

```text
exists_multiset_prod_of_forall_separable_algClosed   SC_1  (𝔸¹ algebraically simply connected)
hasEtaleSplitting_mvPolynomial                       SC_k  (monogenic form)
```

and the hard topological core of the general case is `AlgSpec.isCoveringMap_proj`.

### The immediate next Lean target

Everything for `SCE_1` step (a) is in place except one link, which is the next thing to build:

```text
det (powerMatrix e θ) evaluated at s ≠ 0   ⟺   1, θ, …, θ^(n-1) is a basis of the fibre B/𝔪_s B
```

Route: `B/𝔪_s B` is `ℂⁿ` with the `n` points of `proj⁻¹{s}` as coordinates (that is the fibre
hypothesis of `SCE`), so in those coordinates the specialisation of `powerMatrix e θ` is
`Vandermonde (χ_1 θ, …, χ_n θ)` times the (invertible) change of basis from `e` to the coordinate
basis.  `Matrix.det_vandermonde_ne_zero_iff` then gives the nonvanishing exactly when `θ` separates
the fibre, and a separating `θ` exists because `B` surjects onto the fibre and `ℂ` is infinite.

With that link, step (a) is complete, `AlgSpec.isCoveringMap_proj` applies with no hypotheses beyond
"`B` is free of rank `n` over `ℂ[X]` and every fibre has `n` complex points", and steps (b)–(d)
finish `SCE_1`.

**Cleaner proof of that link, to use.**  Do not go through a change of basis to Vandermonde.
Instead: `det (powerMatrix e θ)` specialises as `(powerMatrix e θ).det.eval s =
det ((powerMatrix e θ).map (evalRingHom s))` by `RingHom.map_det`, and the specialised matrix is the
coordinate matrix of `1, θ, …, θ^(n-1)` in the base-changed basis of the fibre.  If its determinant
vanished, those powers would be linearly dependent over `ℂ` in the fibre, giving a nonzero
`r ∈ ℂ[X]` of degree `< n` with `r(θ) = 0` there; applying the `n` algebra maps gives
`r(χ_i θ) = 0` for `n` distinct values `χ_i θ` (`SplitAlgebraSeparation`), so `r` has `n` roots —
impossible.  Only the base change of a basis is needed, no Vandermonde computation.

`HTGeometry/SplitAlgebraSeparation.lean`, `HTGeometry/SeparatingPowerIndependence.lean` and
`HTGeometry/PowerDeterminantNonvanishing.lean` (all wired, axiom-clean) finish the mathematics of
step (a):

```text
exists_separating_of_surjective        a separating element exists in a split finite algebra
linearIndependent_pow_of_separating    its powers are independent (Vandermonde)
det_powerMatrix_map_ne_zero            ** hence det (powerMatrix e θ) does not vanish at the
                                          parameter **
```

### What the assembly of step (a) still needs

Take `U := {s | (det (powerMatrix e θ)).eval s ≠ 0 ∧ (biResultant p).eval s ≠ 0}`, open, with
`p := algCharpoly ℂ[X] θ`.  Membership of `proj χ₀` in the first set is
`det_powerMatrix_map_ne_zero`; in the second it is separability of `biFibre p (proj χ₀)`, through
`separable_iff_resultant_ne_zero` and `biResultant_eval`.  The one fact still to prove is

```text
biFibre (algCharpoly ℂ[X] θ) s  =  ∏_i (X - C (χ_i θ))        (χ_i the n points of the fibre)
```

— the characteristic polynomial of multiplication by `θ` specialises to the characteristic
polynomial on the fibre, which is split with roots the `χ_i θ`.  With it, separability at `proj χ₀`
is immediate from the distinctness of the `χ_i θ`, and the generation datum is
`exists_aeval_of_det_smul` rewritten through `Algebra.smul_def`.  Then `hchart` is complete and
`AlgSpec.isCoveringMap_proj` applies.

**Correction — the charpoly specialisation is not needed either.**  Separability of
`biFibre p (proj χ₀)` does not require identifying it with `∏ (X - C (χ_i θ))`.  It is enough that
it is monic of degree `n` and has `n` distinct roots, and both are immediate:

* monic of degree `n`: `algCharpoly_monic` and `biFibre_natDegree`;
* each `χ_i θ` is a root: apply `χ_i` to `aeval θ p = 0` and use `AlgSpec.apply_aeval`, which gives
  `biEval p (proj χ_i, χ_i θ) = 0`, i.e. `(biFibre p (proj χ₀)).eval (χ_i θ) = 0`;
* the `χ_i θ` are pairwise distinct by `exists_separating_of_surjective`.

Then `Bottcher.separable_of_distinct_roots` (already in this tree: a degree-`N` complex polynomial
with `N` distinct roots is separable) closes it.  So **step (a) needs no new mathematics at all** —
only the assembly of `AlgebraCharpoly`, `PowerMatrixCramer`, `SplitAlgebraSeparation`,
`PowerDeterminantNonvanishing`, `BivariateSeparableResultant` and `Bottcher.separable_of_distinct_roots`
into the single `hchart` hypothesis of `AlgSpec.isCoveringMap_proj`.

`HTGeometry/SplitParameterSeparability.lean` (wired, axiom-clean):

```text
separable_biFibre_of_separating   ** the monic degree-n relation specialises to a separable
                                     polynomial at a parameter whose fibre separates θ **
```

### The `hchart` assembly, fully determined

Take `θ` separating the fibre at `s₀ := proj χ₀`, `p := algCharpoly ℂ[X] θ`, `g := det (powerMatrix e θ)`
and `U := {s | g.eval s ≠ 0}` (open).  Then:

* `aeval θ p = 0`, `p.Monic`, `p.natDegree = n` — `AlgebraCharpoly` and the rank of `e`;
* `s₀ ∈ U` — `det_powerMatrix_map_ne_zero` with `φ = evalRingHom s₀`, whose `hcomm` hypothesis is
  `AlgSpec.apply_algebraMap`;
* the generation datum on `U` with the *same* `g` for every `b` — `exists_aeval_of_det_smul`
  through `Algebra.smul_def`;
* separability on **all** of `U`, not just at `s₀`: at any `s ∈ U` the generation datum makes
  `AlgSpec.toPlane_injOn` apply, so the `n` points of the fibre over `s` (which exist by the
  cardinality hypothesis) take pairwise distinct values on `θ`; then
  `separable_biFibre_of_separating`.

The only bookkeeping is converting a set of `ncard = n` into an indexed family `Fin n → AlgSpec B`.

`HTGeometry/SplitFibrePointsDistinct.lean` (wired, axiom-clean): `injective_of_surjective_family`
— a jointly surjective family of complex points is pairwise distinct.

**Hypothesis shape to use for the assembly** (decided, so no session re-derives it).  Package the
étale/split-fibre input as one statement:

```lean
hsplit : ∀ s : ℂ, ∃ χ : Fin n → AlgSpec B,
    (∀ i, AlgSpec.proj B (χ i) = s) ∧
    Function.Surjective (fun b : B => fun i => χ i b) ∧
    {χ' : AlgSpec B | AlgSpec.proj B χ' = s} = Set.range χ
```

The cardinality condition of `hchart` then follows from `injective_of_surjective_family` and
`Set.ncard_range_of_injective`, and the separating element at each `s ∈ U` from
`exists_separating_of_surjective`, so no separate `hcard` hypothesis is needed.

`HTGeometry/SplitFibresPackage.lean` (wired, axiom-clean):

```text
SplitFibres B n                 the packaged étale/split hypothesis
ncard_fibre_of_splitFibres      ** it supplies the fibre-cardinality clause of hchart **
```

**Remaining Lean obligations of the assembly** (pure execution, nothing to discover):

```text
exists_chart_of_splitFibres (hn : 1 ≤ n) (e : Module.Basis (Fin n) ℂ[X] B)
    (h : SplitFibres B n) (χ₀ : AlgSpec B) : <the hchart existential>
  θ  := exists_separating_of_surjective applied to the family at s₀ := proj χ₀
  p  := algCharpoly ℂ[X] θ ;  p.natDegree = n needs LinearMap.charpoly_natDegree together with
        Module.finrank_eq_card_basis e
  g  := (powerMatrix e θ).det ;  U := {s | g.eval s ≠ 0}, open since eval is continuous
  s₀ ∈ U            det_powerMatrix_map_ne_zero, hcomm from AlgSpec.apply_algebraMap
  generation on U   exists_aeval_of_det_smul, rewritten by Algebra.smul_def
  separability on U at each s: the generation datum gives AlgSpec.toPlane_injOn, so the family at s
                    has distinct θ-values; then separable_biFibre_of_separating
  cardinality       ncard_fibre_of_splitFibres
```

With `exists_chart_of_splitFibres`, `AlgSpec.isCoveringMap_proj` becomes unconditional for any
finite free `ℂ[X]`-algebra with split fibres, and `SCE_1` continues with steps (b)–(d).

## Lean progress — `SCE_1` steps (a) and (b) are DONE

```text
HTGeometry/SplitFibreChartData.lean   (wired, axiom-clean)
    exists_chart_of_splitFibres           the chart datum, assembled
    isCoveringMap_proj_of_splitFibres     ** the complex-point space of a finite free ℂ[X]-algebra
                                             with split fibres IS a covering space of the parameter
                                             line — no chart hypothesis, unconditional **
HTGeometry/SplitFibreSection.lean     (wired, axiom-clean)
    exists_continuous_section_of_splitFibres   ** and it admits a global continuous section **
```

### Step (c), and the one lemma it needs

For each `b`, `s ↦ σ(s) b` has polynomial growth by `AlgSpec.norm_apply_le_of_monic`, so by
`Bottcher.exists_polynomial_of_entire_polyGrowth` it is a polynomial **once it is known to be
entire**.  Analyticity is local and comes from the chart: on the chart `U` at a point, with its
`θ_U` and `p_U`, the composite `s ↦ (σ s) θ_U` is a *continuous* root branch of `p_U`, hence
analytic — this is `analyticAt_of_continuous_biRoot`, whose proof already uses separability only at
the point in question, so it needs restating with `hsep` on `U` instead of on all of `ℂ`.  Then
`(σ s) b = biEval q_b (s, (σ s) θ_U) / g(s)` is analytic on `U` by `eval_eq_of_gen`.

So step (c) needs exactly one new declaration: the "on `U`" form of
`analyticAt_of_continuous_biRoot`.  Everything else is already proved.

**Step (c)'s one lemma is now in.**  `ComplexAffineLineSimplyConnected.analyticAt_of_continuous_biRoot_at`
— a continuous root branch is analytic at any point where the specialised polynomial is separable
(separability at that single point suffices; the proof already only used it there).  So step (c) is:
on the chart `U` at a point, `s ↦ (σ s) θ_U` is analytic by this lemma, `(σ s) b` is then analytic
by `eval_eq_of_gen`, the growth bound is `AlgSpec.norm_apply_le_of_monic`, and
`Bottcher.exists_polynomial_of_entire_polyGrowth` turns it into a polynomial.  Step (d) then splits
off the resulting `ℂ[X]`-algebra map and inducts on the rank.

## Lean progress — `SCE_1` steps (a), (b), (c) are DONE

```text
HTGeometry/SectionValueAnalytic.lean      analyticAt_section_apply
HTGeometry/SectionValuePolynomial.lean    exists_polynomial_section_apply
HTGeometry/SplitFibreAlgHom.lean
    nonempty_algHom_of_splitFibres
        ** a finite free ℂ[X]-algebra all of whose fibres are split admits a ℂ[X]-algebra
           homomorphism to ℂ[X] — unconditional **
```

### Step (d), the last one, and its elementary proof

For the endgame only the connected case is needed:

```text
B a DOMAIN, free of rank n over ℂ[X], every fibre split  ⟹  n = 1.
```

Proof.  `ψ : B →ₐ[ℂ[X]] ℂ[X]` from step (c) is surjective (it fixes the base).  If `n ≥ 2` its
kernel is nonzero; pick `0 ≠ k ∈ ker ψ`.  Because `B` is a domain, `k` satisfies a monic relation
over `ℂ[X]` with **nonzero constant term** — start from the characteristic polynomial and, while the
constant term vanishes, write `r = X · r'` and cancel `k` in `k · r'(k) = 0`.  Applying `ψ` to that
relation kills every term but the constant one, giving `a₀ = 0`, a contradiction.  Hence `ker ψ = 0`,
`ψ` is an isomorphism, and `n = 1`.

No Krull dimension, no rank comparison — just cancellation in a domain.

## Lean progress — `SCE_1` over ℂ is PROVED

```text
HTGeometry/MonicRelationNonzeroConstant.lean   exists_monic_coeff_zero_ne_zero
HTGeometry/ComplexAffineLineSimplyConnectedGeneral.lean
    rank_eq_one_of_splitFibres
        ** a DOMAIN, finite free over ℂ[X], all of whose fibres are split, has rank one **
```

That is the general (non-monogenic) simple connectedness of the complex affine line — the form an
abstract étale cover can be fed to, which the monogenic `SC_k` could not be.

### Transfer of `SCE_1` to a general algebraically closed characteristic-zero field

The same device as for `SC_1` works, with `Algebra.discr` in the role the fibre resultant played
there.  The point is that the hypothesis must be put in a form preserved by *any* ring
homomorphism:

```text
"every fibre of B is split"  ⟺  Algebra.discr K[X] e  has no zero in K
                             ⟺  (K algebraically closed)  it is a nonzero CONSTANT
```

and a nonzero constant discriminant transports along any embedding.  So: the `n³` structure
constants of `B` in a basis generate a countable algebraically closed subfield `K₀ ⊆ K`
(`CountableFieldComplexEmbedding`), `B` descends to `K₀`, embeds into `ℂ`, and the constancy of the
discriminant carries the split-fibre hypothesis with it.  `rank_eq_one_of_splitFibres` then gives
rank one over `ℂ`, hence over `K₀`, hence over `K`.

The one new ingredient is the equivalence above, i.e. "the fibre of a finite free algebra at `s` is
split iff the discriminant does not vanish at `s`", over an algebraically closed field of
characteristic zero.

**The sub-lemma to build next, stated precisely.**

```text
K algebraically closed of characteristic zero, C a finite free K-algebra with basis b of size n.
    (∃ χ : Fin n → C →ₐ[K] K, jointly surjective and exhausting Hom)   ⟺   Algebra.discr K b ≠ 0
```

Forward: the `n` maps give `C ≅ Kⁿ`, whose trace form in the coordinate basis is the identity, so
the discriminant is a nonzero square of a change-of-basis determinant.  Backward: a nonvanishing
discriminant makes the trace form nondegenerate, so `C` is étale over `K`, and over an algebraically
closed field `Algebra.FormallyEtale.equivPiOfIsSepClosed` splits it into `n` copies.  mathlib
supplies both halves — `Algebra.discr_isUnit_of_basis` /`Algebra.discr_not_zero_of_basis` one way and
`Algebra.Etale.iff_exists_algEquiv_prod` with `equivPiOfIsSepClosed` the other.

With it, `SplitFibres B n ⟺ (Algebra.discr ℂ[X] e).eval s ≠ 0 for all s ⟺ that discriminant is a
nonzero constant`, and the transfer of `SCE_1` to any algebraically closed characteristic-zero field
runs exactly as `AffineLineSimplyConnected` did for `SC_1`.

## Session ledger (final) — 29 modules landed for this card

```text
BivariateRootCovering                 ComplexAffineLineSimplyConnected
CountableFieldComplexEmbedding        BivariateSeparableResultant
AffineLineSimplyConnected             AffineSpaceSimplyConnected
LocalNakayamaMonogenic                AlgebraSpectrumTopology
AlgebraSpectrumFibre                  AlgebraSpectrumChart
AlgebraSpectrumClosed                 AlgebraSpectrumProper
AlgebraSpectrumBijection              AlgebraSpectrumCovering
AlgebraCharpoly                       PowerMatrixCramer
SplitAlgebraSeparation                SeparatingPowerIndependence
PowerDeterminantNonvanishing          SplitParameterSeparability
SplitFibrePointsDistinct              SplitFibresPackage
SplitFibreChartData                   SplitFibreSection
SectionValueAnalytic                  SectionValuePolynomial
SplitFibreAlgHom                      MonicRelationNonzeroConstant
ComplexAffineLineSimplyConnectedGeneral
```

All wired into `GaloisForLFunctions.HTGeometry`, all `[propext, Classical.choice, Quot.sound]`.

**Unconditional headline theorems.**

```text
exists_multiset_prod_of_forall_separable_algClosed   SC_1  over any algebraically closed field of
                                                           characteristic zero
hasEtaleSplitting_mvPolynomial                       SC_k  monogenic form
rank_eq_one_of_splitFibres                           SCE_1 over ℂ — the general, non-monogenic form
```

**Remaining to `criticalGeometricMonodromy = ⊤`:** the `SCE_1` transfer to a general algebraically
closed characteristic-zero field (sub-lemma stated above), `SCE_k` by constant-field descent, `E1`
(branch locus in the chart = the Schur divisor, the discriminant computation), `E2` (Schur inertia
nontrivial and simple).  Then the torus/slice bookkeeping and the single Kummer valuation close `(4)`,
and `projective-horizon-one-step-postcritical-rigidity` follows with no further work.
