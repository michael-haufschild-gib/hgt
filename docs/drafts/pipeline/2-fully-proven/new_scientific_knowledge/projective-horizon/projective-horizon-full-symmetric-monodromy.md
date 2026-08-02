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
