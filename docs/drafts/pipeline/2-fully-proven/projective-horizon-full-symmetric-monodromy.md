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

## Lean progress — `SCE_1` is PROVED over EVERY algebraically closed field of characteristic zero

The transfer sketched in the previous section is done.  Seven new modules, all wired into
`GaloisForLFunctions.HTGeometry`, all `[propext, Classical.choice, Quot.sound]`:

```text
HTGeometry/AlgebraDiscriminantBaseChange.lean
    lmul_baseChange            multiplication by 1 ⊗ x is the base change of multiplication by x
    trace_tensor_one           ** the algebra trace commutes with base change **
    discr_baseChange           ** discr A' (e.baseChange A') = algebraMap A A' (discr A e) **

HTGeometry/SplitFiniteAlgebraDiscriminant.lean
    trace_pi_apply, discr_pi_basisFun, exists_eval_of_algHom_pi
    discr_ne_zero_iff_traceForm_nondegenerate   the basis-free reformulation
    isReduced_of_traceForm_nondegenerate        nondegeneracy kills nilpotents
    nonempty_algEquiv_pi_of_traceForm_nondegenerate
    exists_algHom_family_of_discr_ne_zero
        ** over an algebraically closed field, a finite algebra of rank n with nonzero
           discriminant carries exactly n algebra maps to the field, jointly surjective **
    discr_ne_zero_of_algHom_family              the converse

HTGeometry/ComplexSplitFibresDiscriminant.lean
    splitFibres_of_isUnit_discr       ** IsUnit (discr ℂ[X] e)  ⟹  SplitFibres B n **
    nonempty_algHom_of_isUnit_discr
    rank_eq_one_of_isUnit_discr       SCE_1 over ℂ, discriminant form

HTGeometry/AlgebraicPointDescent.lean
    nonempty_algHom_of_finiteType   ** Zariski's lemma as a descent principle: a nontrivial
                                       finitely generated E-algebra maps to any algebraically
                                       closed extension of E **
    exists_ringHom_descent          ** a ring map A → Ω[X] compatible with E[X] descends to
                                       A → K[X], when A is a finite E[X]-module **

HTGeometry/PolynomialSubfieldDescent.lean
    descentSubalgebra, descentBasis        the E[X]-span of a basis whose structure constants
                                           descend, and its basis
    descentBaseChangeEquiv                 ** K[X] ⊗[E[X]] B₀ ≅ B **
    discr_descentBasis                     ** algebraMap E[X] K[X] (discr E[X] e₀) = discr K[X] e **
    isUnit_of_isUnit_map                   a unit downstairs from a unit upstairs

HTGeometry/DomainAlgHomRankOne.lean
    rank_eq_one_of_algHom     ** a domain finite free over a domain with a section has rank one **

HTGeometry/AffineLineSimplyConnectedEtale.lean
    rank_eq_one_of_isUnit_discr_algClosed
        ** SCE_1 : over ANY algebraically closed field of characteristic zero, a DOMAIN that is
           finite free over K[X] with unit discriminant has rank one — the affine line has no
           nontrivial connected finite étale cover, with no monogenicity assumption **
```

### The three devices that made the transfer work, recorded so no session re-derives them

1. **The étale hypothesis must be a single ring element.**  `SplitFibres` (a family of complex
   points over every parameter) does not transport along a ring homomorphism; `IsUnit (discr)`
   does.  `SplitFiniteAlgebraDiscriminant` is exactly the dictionary between the two, and both of
   its directions go through "the trace form is nondegenerate", which is basis-free — so no
   change-of-basis determinant ever appears.

2. **The domain hypothesis must never be transported.**  `B₀ ⊗ ℂ` being a domain is *geometric*
   integrality and is a hard theorem.  It is not needed: over `ℂ` one only extracts a **`ℂ[X]`-algebra
   map** (`nonempty_algHom_of_isUnit_discr`), which is a piece of data with finitely many
   coefficients; that datum is descended, and the domain hypothesis is used only at the very end,
   over `K`, by `rank_eq_one_of_algHom`.  This removes the need for any Lefschetz principle.

3. **Zariski's lemma replaces the Nullstellensatz plumbing.**  To descend the map one does *not*
   set up a polynomial system: the finitely many coefficients of the images of a module basis
   generate a finitely generated `F`-subalgebra `R ⊆ ℂ`, the map factors through `R[X]` because a
   basis generates, and `Nonempty (R →ₐ[F] K)` follows from "a field is a Jacobson ring" plus
   `IsAlgClosed.lift`.  No degree bounds, no `MvPolynomial` ideals.

A fourth, purely technical, trap: `haveI : Algebra R S := inferInstance` introduces an **opaque**
local instance and silently breaks definitional equality with the global one, so `rw` with a
base-change lemma fails with "did not find an occurrence" on a syntactically identical pattern.
Never restate an instance that already resolves.

### Status of the whole programme after this step

```text
SC_1  over any algebraically closed characteristic-zero field   DONE
SC_k, monogenic form                                            DONE
SCE_1 over ℂ                                                    DONE
SCE_1 over any algebraically closed characteristic-zero field   DONE   <-- this session
SCE_k (all of affine space)                                     OPEN
E1  branch locus in the chart = the Schur divisor               OPEN
E2  Schur inertia nontrivial and simple                         OPEN
torus/slice bookkeeping and the final Kummer valuation          OPEN  (no new mathematics)
```

### `SCE_1` now also exposes the section itself

`AffineLineSimplyConnectedEtale` was refactored so that the section is available **without** the
domain hypothesis, since that is what the multivariable induction consumes:

```text
nonempty_algHom_of_isUnit_discr_algClosed
    ** over ANY algebraically closed field of characteristic zero, a finite free K[X]-algebra with
       unit discriminant admits a K[X]-algebra map to K[X] **
rank_eq_one_of_isUnit_discr_algClosed          (the domain corollary)
```

## The route to `SCE_k`, decided and Galois-free

Several routes were considered and only one survives without a large field-theoretic
infrastructure.  Recorded in full so no session re-derives them.

**Ruled out.**

* *Restriction to a general line.*  Needs Bertini connectivity — the original blocker.
* *Purity of the branch locus.*  Would be needed to turn "unramified in codimension one" into
  "étale"; a deep theorem, and mathlib has none of it.
* *Constant-field theorem via Galois descent* (`L ⊆ F̄(w)`, `L = (L ∩ F̄)(w)`).  Correct, and the
  finite-Galois reduction is available (the coefficients of the section generate a finite extension
  of `F`), but it needs the Galois correspondence for `F₂(w)/F(w)` and Galois descent for vector
  spaces — several hundred lines of pure plumbing.
* *Lifting idempotents from `B/wB` to `B`.*  Fails: `(w)` is neither nilpotent nor complete, and
  lifting to `R[[w]]` gives no algebraicity.
* *Topological argument over `ℂ^k`.*  Would need the several-variable holomorphic implicit function
  theorem and a rebuild of the whole covering-space stack in `k` parameters.

**The route to build: a locally nilpotent derivation with a slice.**

For the inductive step write `A = R[w]` with `R = MvPolynomial (Fin (k-1)) K`, and let `B` be a
domain, finite free of rank `n` over `A`, with `IsUnit (Algebra.discr A e)`.

```text
P1  separability idempotent.  With e a basis and f its dual basis for the trace form (invertible
    Gram matrix, because the discriminant is a unit), p := Σ e_i ⊗ f_i ∈ B ⊗_A B satisfies
    Σ e_i f_i = 1     and     (b ⊗ 1) p = (1 ⊗ b) p
    — both are one-line computations with the trace form.  Consequence, by the classical
    two-line argument: **every A-derivation of B is zero**, i.e. a lift of a derivation of A is
    unique.
P2  existence of the lift.  B is separable over A, hence formally smooth, so the derivation
    d/dw of A lifts to an R-derivation ∂ of B with ∂ w = 1.
P3  slice theorem.  If ∂ is a locally nilpotent derivation of a ℚ-algebra B and ∂ s = 1, then
    B = (ker ∂)[s] and s is transcendental over ker ∂.  Elementary induction on the nilpotency
    order, using b - (∂^N b) s^N / N!.
P4  splitting form of SCE_1.  Over an algebraically closed field E of characteristic zero, a finite
    free E[X]-algebra with unit discriminant is isomorphic to E[X]^n.  From the section already
    proved: the trace form is nondegenerate, so the section is Tr(ε · —) for a unique ε; ε is
    idempotent because it is idempotent in every fibre and E is infinite; split off and induct.
P5  local nilpotence, then the induction.  With F = Frac R and F̄ its algebraic closure,
    B ⊗_R F̄ ≅ F̄[w]^n by P4, and by P1 the derivation ∂ ⊗ 1 is the componentwise d/dw, which is
    locally nilpotent; B embeds in B ⊗_R F̄ because B is free over R.  So ∂ is locally nilpotent on
    B, P3 gives B = C[w] with C = ker ∂, hence C ≅ B/wB is a domain, finite free of rank n over R
    with unit discriminant (base change of the discriminant), and the induction closes.
```

The base case `k = 0` is `exists_algHom_family_of_discr_ne_zero` together with "a domain that is a
finite product of copies of a field has rank one".

Note what P5 avoids: no Galois descent, no constant-field theorem, no purity — local nilpotence is
checked after base change to `F̄`, where the derivation is *forced* to be `d/dw` by the uniqueness
of P1, and nilpotency of an element is detected in any faithful extension.

## Lean progress — the `SCE_k` engine, part 1: seven more modules

All wired into `GaloisForLFunctions.HTGeometry`, all axiom-clean.

```text
HTGeometry/LocallyNilpotentDerivationSlice.lean
    derivationKernel, iterate_deriv_pow, exists_polynomial_of_iterate_eq_zero
    aeval_slice_injective
    bijective_aeval_of_locallyNilpotent, sliceAlgEquiv
        ** SLICE THEOREM: a locally nilpotent derivation of a ℚ-algebra with D s = 1 makes the
           algebra the polynomial ring (ker D)[s] **

HTGeometry/TraceDualBasisSeparability.lean
    traceDual, trace_mul_traceDual, eq_zero_of_trace_basis_mul_eq_zero
    sum_mul_traceDual        ∑ᵢ eᵢ fᵢ = 1
    mul_traceDual            b fᵢ = ∑ⱼ (e.repr (b eⱼ) i) fⱼ
    derivation_eq_zero       ** a finite free algebra with unit discriminant has NO nonzero
                                derivations over the base — uniqueness of derivation lifts **

HTGeometry/EtaleDerivationLift.lean
    sum_swap_traceDual       the separability identity as a swap of bilinear arguments
    coeffDeriv, theta, theta_cocycle, phi, phi_key
    liftDerivation           ** EXISTENCE: every derivation of the base lifts to a finite free
                                algebra with unit discriminant (Hochschild coboundary, no tensor
                                products) **
    liftDerivation_algebraMap, derivation_ext

HTGeometry/SectionIdempotent.lean
    trace_traceDual_mul, dual_expansion, dual_expansion'
    sectionIdem              ε := ∑ᵢ ψ(eᵢ) • fᵢ
    trace_sectionIdem_mul    Tr(ε b) = ψ b
    sectionIdem_mul          ** ε b = ψ b • ε **
    apply_sectionIdem        ** ψ ε = 1  (apply ψ to ∑ eᵢ fᵢ = 1) **
    sectionIdem_idem         ** hence ε² = ε **

HTGeometry/ProductAlgebraDiscriminant.lean
    isUnit_discr_of_isUnit_discr   unit-ness of the discriminant is basis-independent
    trace_prod_apply, discr_prod_singleton   the trace form of A × B' is an orthogonal direct sum

HTGeometry/SectionQuotientSplit.lean
    sectionProdEquiv         ** B ≃ₐ[A] A × (B ⧸ (ε)) **
    finite/torsionFree/finrank_sectionQuot
    exists_basis_sectionQuot ** over a PID the complement is free of rank one less, with unit
                                discriminant **

HTGeometry/AffineLineEtaleSplit.lean
    finSuccProdAlgEquiv, emptyAlgEquiv
    nonempty_algEquiv_pi_of_isUnit_discr
        ** over ANY algebraically closed field of characteristic zero, a finite free E[X]-algebra
           with unit discriminant is isomorphic to E[X]ⁿ — the full splitting, not just the
           connected case **
```

### The two discoveries that made this cheap, recorded

1. **The section idempotent is elementary.**  It was expected that `ε² = ε` would have to be checked
   fibre by fibre (the fibres are split, so `ε` is a coordinate idempotent there, and an infinite
   base field then forces the identity).  That is unnecessary: `ε b = ψ b • ε` follows by expanding
   `ε b` in the dual basis, and `ψ ε = 1` follows by applying `ψ` to `∑ᵢ eᵢ fᵢ = 1`.  Both are three
   lines, and `ε² = ψ ε • ε = ε`.

2. **`∂ ε = 0` for free.**  Differentiating `ε b = ψ b • ε` at `b = ε` gives `2 ε ∂ε = ∂ε`;
   multiplying by `ε` gives `ε ∂ε = 0`, hence `∂ε = 0`.  So the derivation respects the idempotent
   splitting with no further argument.  (Recorded for the next step; the splitting theorem above
   makes it unnecessary in the end, since after splitting the derivation is *forced* to be the
   componentwise `d/dw`.)

### What remains of `SCE_k`

```text
polyDeriv                 d/dX as a Derivation R R[X] R[X]                       TODO (small)
derivation_eq_zero, module form   Derivation A B M = 0 for any B-module M         TODO (small)
locallyNilpotent           over an algebraically closed field: transport the lift through
                           nonempty_algEquiv_pi_of_isUnit_discr, where the lift is forced by
                           derivation_ext to be the componentwise derivative                TODO
base-change compatibility  ∂̄ (1 ⊗ b) = 1 ⊗ ∂ b, by the module form of derivation_eq_zero   TODO
SCE_k induction            MvPolynomial.finSuccEquiv, then: local nilpotence over F̄ ⟹ slice
                           theorem ⟹ B = C[w] ⟹ C = B/wB is a domain, finite free of rank n
                           over R with unit discriminant ⟹ induction                        TODO
```

## Lean progress — `SCE_k` IS PROVED.  Affine space is algebraically simply connected.

The step the card identified as *"the single new piece of mathematics"* is done, unconditionally,
over every algebraically closed field of characteristic zero, in the general (non-monogenic) form.

```text
HTGeometry/AffineSpaceEtaleRankOne.lean
    hasEtaleRankOne_of_ringEquiv
    hasEtaleRankOne_mvPolynomial
    rank_eq_one_of_isUnit_discr_mvPolynomial
        ** SCE_k : over an algebraically closed field of characteristic zero, a DOMAIN that is
           finite free over MvPolynomial (Fin k) K with unit discriminant has rank one **
```

`[propext, Classical.choice, Quot.sound]`, like every module below it.

### The full stack, in dependency order

```text
TraceDualBasisSeparability      dual basis, ∑ eᵢ fᵢ = 1, derivation_eq_zero   (uniqueness of lifts)
EtaleModuleDerivation           the same, for derivations into any module     (uniqueness across
                                                                               a base change)
EtaleDerivationLift             liftDerivation                                (existence of lifts)
SectionIdempotent               ε with Tr(ε b) = ψ b,  ε b = ψ b • ε,  ψ ε = 1,  ε² = ε
ProductAlgebraDiscriminant      discr is basis-independent; discr (A × B') = discr B'
SectionQuotientSplit            B ≃ A × (B ⧸ (ε)); over a PID the complement is again étale
AffineLineEtaleSplit            B ≅ E[X]ⁿ for E algebraically closed          (full splitting)
LocallyNilpotentDerivationSlice B = (ker D)[s] for a locally nilpotent D with a slice
AffineLineEtaleLocallyNilpotent the lift of d/dX is locally nilpotent over an algebraically
                                closed field
PolynomialEtaleLocallyNilpotentDomain   ... and over any characteristic-zero domain
PolynomialFibreQuotientBasis    the fibre B ⧸ (w) is finite free over R with
                                discr = (discr upstairs).eval 0
EtaleRankOnePolynomialStep      HasEtaleRankOne R → HasEtaleRankOne R[X]      (𝔸¹-invariance)
AffineSpaceEtaleRankOne         the induction on the number of variables
```

### The mathematical route, recorded

The inductive step is `𝔸¹`-invariance of finite étale covers, proved by a **locally nilpotent
derivation with a slice** — no Galois descent, no constant-field theorem, no purity of the branch
locus, and no several-variable complex analysis.

```text
B a domain, finite free of rank n over R[X] with unit discriminant, R a char-0 domain.
1. The trace-dual basis makes B separable over R[X]: ∑ eᵢ fᵢ = 1 and b fᵢ = ∑ⱼ (repr) fⱼ.
   Hence A-derivations of B vanish (uniqueness) and the Hochschild defect of "differentiate the
   coordinates" is a coboundary (existence).  So d/dX lifts uniquely to ∂ on B, with ∂ w = 1.
2. ∂ is locally nilpotent.  Base change to E = alg. closure of Frac R: there B ⊗ E[X] ≅ E[X]ⁿ by
   the full splitting theorem, and by uniqueness the lift there is the componentwise d/dX, which
   kills polynomials.  Nilpotency descends because b ↦ 1 ⊗ b is injective.
3. Slice theorem: B = C[w] with C = ker ∂.
4. Reduction mod w is an isomorphism C ≅ B ⧸ (w): surjective by the Taylor expansion, injective
   because C c = X q forces c = 0.  So the fibre is a DOMAIN.
5. The fibre is finite free of rank n over R with discriminant the value at 0 of the discriminant
   upstairs, hence a unit.  Induction.
```

The full splitting theorem of step 2 is itself an induction on the rank: the section supplied by
`AffineLineSimplyConnectedEtale` has an idempotent `ε = ∑ᵢ ψ(eᵢ) fᵢ` (elementary: `ε b = ψ b • ε`
and `ψ ε = 1`), `B ≃ A × (B ⧸ (ε))`, and the complement is again finite free with unit
discriminant.

### What remains for the card

```text
SC_1, SC_k monogenic, SCE_1 over ℂ, SCE_1 over any alg. closed char-0 field   DONE
SCE_k                                                                        DONE  <-- this session
E1  branch locus in the chart = the Schur divisor (the discriminant computation)   OPEN
E2  Schur inertia nontrivial and simple                                            OPEN
torus/slice bookkeeping and the final Kummer valuation                             OPEN
```

With `SCE_k` in hand, `E5` of the endgame is now a Lean theorem, and the remaining obligations are
the two geometry inputs `E1`, `E2` that the card already isolates, plus bookkeeping.

## Lean progress — Jordan's criterion on the ACTUAL sheets

`CriticalMonodromyJordan` states Jordan's theorem for the abstract occupation states; the actual
monodromy group acts on `criticalGeometricSheet`, so the criterion is restated there.

```text
HTGeometry/CriticalGeometricMonodromyJordan.lean   (wired, axiom-clean)
    finite_criticalGeometricSheet
        the sheet set is finite (finite-dimensionality of the source over the observation field)
    criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap
    criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_reducedFibre_degree
        ** primitivity + the Schur reduction-degree bound  ⟹  criticalGeometricMonodromy = ⊤ **
```

So `(4)` is now *exactly* two Lean statements away:

```text
(i)  Nontrivial (criticalSchurInertiaGroup K hm hn)                       -- E2, half one
(ii) Nat.card (criticalGeometricSheet K m n)
        ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard + 1
                                                                          -- E2, half two
(iii) MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
        (criticalGeometricSheet K m n)                                    -- E1 + E3..E7
```

Everything else in the chain is already unconditional in the tree: transitivity
(`criticalGeometricMonodromy_isPretransitive`), the passage from the degree bound to a transposition
(`exists_criticalGeometricMonodromy_isSwap_of_reducedFibre_degree`), the Jacobian/Schur-divisor
identity (`criticalSourceReciprocalJacobian_det_eq_schurRamification`), the divisorial order-one
statement (`addVal_criticalSchurJacobianDetElement_eq_one`), and now `SCE_k`
(`rank_eq_one_of_isUnit_discr_mvPolynomial`), which is what `E5` consumes.

### The remaining programme, in Lean terms

```text
(i)   Nontrivial Schur inertia.  The Jacobian determinant is a uniformizer of the source Schur
      valuation ring (addVal_criticalSchurJacobianDetElement_eq_one), so the different of the
      extension at that place is nontrivial, so the place ramifies, so inertia ≠ 1.  What must be
      built is the ramification-theoretic bridge "different ≠ 1 ⟹ inertia ≠ 1" for the DVR already
      constructed in CriticalSchurValuationDVR.

(ii)  The degree count.  Generic corank one of the rectangular Schur divisor
      (CriticalSchurGenericCorank) says the fold is simple, i.e. the reduction map on sheets is
      injective except for one identified pair; that is exactly the stated `+ 1`.

(iii) Primitivity.  This is E1 followed by E3–E7:
        E1  the branch locus of J/O inside the chart is the Schur divisor — the Jacobian identity
            above plus the statement that a place of O not below the Schur divisor is unramified in
            J, which is the standard "étale where the Jacobian is a unit" criterion;
        E3  the block field M is then unramified at every height-one prime of the chart ring;
        E4  T-equivariance moves that to every height-one prime of the slice K[w₁..w_{L-2}];
        E5  SCE_k  ⟹  M_S = O_S                                  ** now available in Lean **
        E6  M ⊆ O' = O(c^{1/L}), cyclic, and v_m(c) = 1 forces M = O;
        E7  the block system is trivial, so the action is primitive.
```

Steps `E4`, `E6` are valuation bookkeeping on objects the tree already builds
(`CriticalRawCoordinateValuation`, `CriticalReciprocalCoordinateValuation`,
`CriticalSourceKummerObstruction`, `TorusKummerExponents`); `E1` and `E3` are the ramification
bridge that `(i)` also needs.  So the whole card reduces to **one** piece of infrastructure — the
ramification dictionary for the Schur place — plus bookkeeping.

### Reading of the three remaining obligations, for the next session

**`Nontrivial (criticalSchurInertiaGroup K hm hn)`.**  The group is literally
`(criticalNormalClosureSchurValuationSubring K hm hn).inertiaSubgroup (criticalObservationField K m n)`
— mathlib's `ValuationSubring.inertiaSubgroup`.  mathlib carries no `|I| = e` statement, so the
nontriviality must be produced directly: exhibit one nontrivial element of the decomposition group
acting trivially on the residue field.  The tree already supplies the ingredients on the source
side: `criticalSchurJacobianDetElement` is a uniformizer of the source Schur valuation ring
(`addVal_criticalSchurJacobianDetElement_eq_one`, `irreducible_criticalSchurJacobianDetElement`),
and `CriticalSchurValuationDVR` builds the DVR and the comparison
`criticalNormalClosureSchurValuationSubring_comap_observation`.  The missing link is the standard
"a uniformizer of the base has valuation `e > 1` upstairs ⟹ the residue map on the decomposition
group is not injective", i.e. a ramification dictionary for one valuation subring of a normal
extension.  Nothing about the horizon is involved; it is a general fact about
`ValuationSubring.inertiaSubgroup` and should be built as its own reusable module.

**The degree count.**  `finrank_ker_criticalSchurGenericMatrix_eq_one` (generic corank one) is
already Lean.  What is needed is §3 of this card in Lean: at a generic point of the Schur divisor
the conormal line determines the projective tangent pair `(U,V)`, `U(0) ≠ 0` and `V(0) ≠ 0`, so `U`
and `V` are coprime and the syzygy `D₀V + E₀U = 0` forces `D₀ = E₀ = 0`, i.e. exactly two sheets
meet.  That is the paper proof already written above; it is a computation with the low-degree
polynomial pairs of `(5)`–`(10)`, not new mathematics.

**Primitivity.**  `E1` needs the same ramification dictionary as the first item (a place where the
Jacobian is a unit is unramified), `E3`–`E4` are formal consequences, `E5` is now
`rank_eq_one_of_isUnit_discr_mvPolynomial`, and `E6`–`E7` are the Kummer valuation and the block
bookkeeping, on objects the tree already builds.

**Consequently the whole card, and with it `projective-horizon-one-step-postcritical-rigidity`,
rests on one missing reusable module — the ramification dictionary for a valuation subring of a
normal extension — plus the §3 conormal computation and bookkeeping.**

## Lean progress — the ramification dictionary was already in the tree

The "missing reusable module" identified above turned out to be **already present**, in two pieces
that had not been chained:

```text
natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn   (CriticalSchurIntegralClosurePlace)
criticalSchurIdealInertiaToInertia_injective                  (CriticalSchurIdealInertiaTransport)
```

Chaining them is `HTGeometry/CriticalSchurRamificationInertia.lean` (wired):

```text
nontrivial_of_injective_monoidHom
nontrivial_criticalSchurInertiaGroup_of_ramificationIdx
    ** 2 ≤ ramificationIdxIn  ⟹  Nontrivial (criticalSchurInertiaGroup) **
exists_criticalGeometricMonodromy_isSwap_of_ramification_of_degree
criticalGeometricMonodromy_eq_top_of_ramification_of_degree_of_isPreprimitive
    ** ramification + reduction-degree count + primitivity  ⟹  criticalGeometricMonodromy = ⊤ **
```

So `(4)` is now literally three named geometric inputs, each a single Lean statement:

```text
(R)  2 ≤ Ideal.ramificationIdxIn
        (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
        (CriticalSchurNormalIntegralClosure K hm hn)
(D)  Nat.card (criticalGeometricSheet K m n)
        ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard + 1
(P)  MulAction.IsPreprimitive (criticalGeometricMonodromy K m n) (criticalGeometricSheet K m n)
```

**(R) and (D) are the same geometry** — the simple fold of §3.  `(R)` says the observation
uniformizer at the Schur place pulls back to the square of a source uniformizer; `(D)` says exactly
two sheets meet there.  Both are consequences of generic corank one
(`finrank_ker_criticalSchurGenericMatrix_eq_one`, already Lean) together with the conormal argument
of §2–§3, whose only remaining content is the coprimality of the tangent pair `(U,V)` at the generic
fold and the syzygy `D₀V + E₀U = 0`.

**(P)** is `E1`–`E7`; its hard input `E5` is now `rank_eq_one_of_isUnit_discr_mvPolynomial`.

The lesson, recorded so no session repeats the search: **before building ramification
infrastructure, check `CriticalSchurIntegralClosurePlace` and `CriticalSchurIdealInertiaTransport`
— the ideal-theoretic side of the Schur place is already complete, including `|I| = e`.**

### The route to `(R)`, for the next session

`(R)` is `2 ≤ Ideal.ramificationIdxIn (maximalIdeal (CriticalSchurNormalBaseRing …))
(CriticalSchurNormalIntegralClosure …)`.  The intended proof is the different–discriminant
dictionary in the tame case:

```text
addVal_criticalSchurJacobianDetElement_eq_one      (already Lean)
      the reciprocal Jacobian determinant is a UNIFORMIZER of the source Schur DVR
  ⟹  the different of the extension at that place has valuation exactly 1
  ⟹  (tame, since char 0)   d = e − 1   ⟹   e = 2
```

mathlib carries the different in `Mathlib/RingTheory/DedekindDomain/Different.lean`
(`differentIdeal`, `aeval_derivative_mem_differentIdeal`, and the conductor comparison).  What must
be built is the bridge between the tree's concrete Jacobian element and `differentIdeal`, i.e. the
statement that for a monic generator of the extension the different is generated by the derivative
of its minimal polynomial — which is exactly `aeval_derivative_mem_differentIdeal` plus equality in
the monogenic case.  The tree already provides the monogenic generator machinery
(`CriticalSourcePrimitiveGenerator`, `ArtinianLocalMonogenic`,
`exists_adjoin_eq_top_of_principal_nilpotent`).

Note that `(R)` and `(D)` are the two halves of the same simple-fold statement; proving the
different has valuation one gives `e = 2` and, by `|I| = e`, an inertia group of order two, which
by `exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two_of_card` needs only
`(D)` to conclude.  So the two remaining local inputs are:

```text
different at the Schur place has valuation one        ⟹ (R), and |I| = 2
exactly two sheets meet over the Schur place          ⟹ (D)
```

### §3's ingredients are already Lean — what `(D)` still needs

A second search of the tree (do this before writing anything for `(D)`):

```text
finrank_ker_criticalSchurGenericMatrix_eq_one     (CriticalSchurGenericCorank)
      generic corank one of the rectangular Schur Toeplitz matrix
criticalSchurGeneric_ker_coord_zero_ne_zero       (CriticalSchurKernelLeadingCoefficient)
      ** every nonzero generic kernel vector has nonzero zeroth coordinate **
      — this is exactly "U(0) ≠ 0" of §3, already proved
criticalSchur_scale_not_mem_ramificationIdeal     (CriticalSchurTailIntegrality)
criticalGeometricSheetToSchurFibre_injective      (CriticalSchurSheetLift)
criticalGeometricSheetToSchurReducedFibre_inertia_invariant   (CriticalSchurReducedSheetInvariance)
```

So of §3 the tree owns: corank one, `U(0) ≠ 0`, the sheet-to-fibre injectivity before reduction,
and the inertia invariance of the reduction.  What `(D)` still needs is the *last* step of §3:
from `U(0) ≠ 0` and the degree-zero part of `(6)` deduce `V(0) ≠ 0`, hence `U`, `V` coprime, hence
by Euclid on the syzygy `D₀V + E₀U = 0` that `D₀ = E₀ = 0` — i.e. two sheets with the same
reduction are equal unless they are the identified pair.  That is a computation with the low-degree
pairs of `(5)`–`(10)`, entirely inside the objects the tree already defines.

Recorded so that no session re-proves corank one or `U(0) ≠ 0`.

### Inventory of the card's numbered claims against the Lean tree

```text
(1)  the critical raw/reciprocal tail map          definitional        (CriticalObservationField,
                                                                        CriticalReciprocal*)
(2)  the open chart x₀ pₘ qₙ ≠ 0, no escape        DONE                (CriticalBiprojectiveBoundary,
                                                                        PostcriticalNotMemField)
(3)  generic degree D = choose(L, m)               ** DONE **          finrank_criticalSourceField_eq_
                                                                        criticalHorizonMultiplicity ,
                                                                        natCard_criticalGeometricSheet_eq_
                                                                        criticalHorizonMultiplicity
(4)  Mon_geom = S_D                                OPEN                reduced to (R), (D), (P)
     the Schur divisor maps 1–1 to the branch       OPEN                = (D) together with E1
     the meridian is ONE transposition              OPEN                = (R) with |I| = e = 2
```

So `(1)`–`(3)` of the theorem statement are unconditional Lean today; the whole remaining content
of the card is the single displayed equation `(4)` together with its two accompanying sentences,
and all three reduce to `(R)`, `(D)`, `(P)` as listed above.

### §3 and §4 as Lean targets, written out

**§3 → `(D)` and `(R)`.**  Work with the two low-degree pairs of `(5)`–`(6)` inside the jet algebra
the tree already defines.  The steps, in order, each a separate lemma:

```text
3a  U(0) ≠ 0 at the generic fold                   ALREADY LEAN
        criticalSchurGeneric_ker_coord_zero_ne_zero
3b  V(0) ≠ 0                                       from the degree-zero part of (6) and 3a
3c  U, V coprime                                   from 3a, 3b and generic corank one
        (a common factor g has g(0) ≠ 0, so g is invertible mod t^L, and dividing (6) by g would
         give a second low tangent pair, contradicting finrank_ker_… = 1)
3d  the syzygy (10) ⟹ (11)                         Euclid, from 3c
3e  (12) and the marked-tail nonvanishing (13)     the marked coefficient is already Lean:
        reduced_criticalNormalClosureSchurReciprocalTailIntegral_coeff_marked_ne_zero
3f  contradiction by trailing-degree multiplicativity  ⟹ the two states coincide
        ⟹ ramification-to-branch degree one ⟹ (D), and the local index is 2 ⟹ (R)
```

**§4 → `(P)`.**  With the transposition in hand:

```text
4a  H := normal closure of the meridian in G; its orbits form a block system for G
4b  a nontrivial block gives a nontrivial finite étale cover of the chart (𝔾ₘ)² × 𝔸^(L-2)
4c  torus Kummer: every such cover has a cyclic quotient z^r = pₘ^a qₙ^b        (15)
        the tree owns TorusKummerExponents, UfdPowerDescent, LocalizationTwoPrimeUnits
4d  the slice factor 𝔸^(L-2) contributes nothing                ** SCE_k, now Lean **
        rank_eq_one_of_isUnit_discr_mvPolynomial
4e  v_m(pₘ) = 1, v_m(qₙ) = 0                                     (16)
        CriticalRawCoordinateValuation, CriticalReciprocalCoordinateValuation
4f  r ∣ a and r ∣ b, contradiction with (15)  ⟹ one block  ⟹  IsPreprimitive  =  (P)
```

Every named module in `4c`–`4e` already exists; `4d` is the theorem proved this session.  So `(P)`
is bookkeeping over existing assets plus `4a`–`4b`, which are pure group theory and the definition
of the block cover.

## Correction — §2 and §3 are almost entirely Lean already

A third search of the tree (this is the third time the corpus turned out to own what looked
missing; search first, always) shows §2 and §3 are formalized as general lemmas:

```text
conormal_determines_tangent, conormal_determines_tangent_smul   (ConormalTangentDetermination)
      §2: the conormal line determines the projective tangent pair
syzygy_of_shared_tangent, eq_zero_of_tangent_syzygy             (TrailingDegreeSyzygy)
exists_cofactor_of_syzygy                                        (ProjectiveHorizonConormalPairing)
      §3 (10)–(11): Euclid on the syzygy
criticalFibre_eq_of_shared_coprime_tangent                       (CriticalFibreSharedTangentRigidity)
      ** §3's conclusion: two states of one critical fibre with the same COPRIME nonzero vertical
         tangent pair are equal — the whole of §3 modulo coprimality **
tangent_relation_of_common_factor, dvd_of_mul_dvd_of_coeff_zero_ne_zero  (HorizonTruncationCancel)
      dividing the truncated tangent relation by a factor invertible at the origin
criticalSchurGeneric_ker_coord_zero_ne_zero                      (CriticalSchurKernelLeadingCoefficient)
      §3: U(0) ≠ 0
finrank_ker_criticalSchurGenericMatrix_eq_one                    (CriticalSchurGenericCorank)
      §3: generic corank one
```

The only two general steps that were genuinely absent are now Lean
(`HTGeometry/CriticalSchurTangentConstantTerm.lean`, wired):

```text
criticalReciprocalInfinitesimal_coeff_zero_ne_zero
      ** §3 step 3b: V(0) ≠ 0, since dY = −(Y² dX) **
isCoprime_of_low_tangent_unique
      ** §3 step 3c: a low tangent pair with nonzero constant terms, unique up to scale, is
         COPRIME — a common factor divides the relation out, and uniqueness forces it to be a unit **
```

So §3 is complete as a chain of general lemmas.  What is left for `(D)` is **wiring**: instantiate
the uniqueness hypothesis of `isCoprime_of_low_tangent_unique` from
`finrank_ker_criticalSchurGenericMatrix_eq_one`, and apply
`criticalFibre_eq_of_shared_coprime_tangent` to two sheets with the same Schur reduction.  No new
mathematics.

## Sharpened `(D)`, and §4's inventory

**`(D)` is best taken in collision form.**  The transposition criterion consumes
`collisionSupport ≤ 2` directly, so the degree count is an unnecessary detour;
`HTGeometry/CriticalSchurRamificationInertia.lean` now also carries

```text
criticalGeometricMonodromy_eq_top_of_ramification_of_collision_of_isPreprimitive
    ** ramification + (collisionSupport …).ncard ≤ 2 + primitivity ⟹ criticalGeometricMonodromy = ⊤ **
```

and the identity to keep in mind is

```text
#sheets − #(reduced fibre) = #(ramified places above the Schur place)
```

so `(D)` is literally §3's conclusion "the ramification-to-branch degree is one".

**§4's algebraic core is also already in the tree.**

```text
dvd_exponents_of_eq_pow_torusChart              (LocalizationTwoPrimeUnits)
      ** (15)–(17): a unit of the chart that is an r-th power has both monomial exponents
         divisible by r — this is §4's contradiction, for (𝔾ₘ)² × 𝔸ᴸ **
criticalRawCoordinateFieldValuation_X_self      (CriticalRawCoordinateValuation)
      ** (16): the defining raw coordinate has divisorial order one **
connectedFiniteTorusChartCover_exists_nontrivial_cyclic_character   (TorusChartConnectedCover)
      (15): Kummer-character reduction for a connected finite cover of the torus chart
UfdPowerDescent, TorusKummerExponents
```

So of §4 only `4a`–`4b` remain: the orbits of the normal closure of the meridian form a block
system, and a nontrivial block yields a finite étale cover of the chart.  `4d`, the slice factor,
is `rank_eq_one_of_isUnit_discr_mvPolynomial`, proved this session.

**Net position.**  Of the card's four sections, §1 and §2 are Lean, §3 is Lean except for the
wiring of coprimality into the actual Schur fibre, and §4 is Lean except for `4a`–`4b`.  The three
named obligations `(R)`, `(D)`, `(P)` are all now assemblies of existing theorems rather than new
mathematics.

## A better endgame — `(4)` from ONE statement

`TranspositionTransitive.eq_top_of_isSwap_of_transitive` was already in the tree ("a transitive
group generated by transpositions is the full symmetric group"), and transitivity of the actual
monodromy is already unconditional.  Chaining them
(`HTGeometry/CriticalGeometricMonodromySwapGeneration.lean`, wired):

```text
criticalGeometricMonodromy_eq_top_of_generated_by_swaps
    (hS : ∀ f ∈ S, f.IsSwap) (hgen : criticalGeometricMonodromy K m n = Subgroup.closure S) :
      criticalGeometricMonodromy K m n = ⊤
```

**This supersedes the three-input packaging.**  `(4)` now follows from the single statement

```text
(G)  the actual geometric monodromy group is generated by transpositions
```

with no Jordan, no primitivity, no block system, no reduction-degree count, and no separate
ramification hypothesis — `(R)`, `(D)` and `(P)` are all consequences of `(G)` rather than
independent inputs.  Geometrically `(G)` is §4's "the only interior branch inertia lies in `H`",
i.e. `E1` (the branch locus in the chart is the Schur divisor) together with `E3`–`E5` (the maximal
unramified subcover of the chart is trivial), whose hard input `E5` is now
`rank_eq_one_of_isUnit_discr_mvPolynomial`.

The primitivity packaging is kept in `CriticalSchurRamificationInertia` and
`CriticalGeometricMonodromyJordan` as the alternative route; whichever of the two is easier to
supply geometrically now closes the card, and with it
`projective-horizon-one-step-postcritical-rigidity`.

## §4's contradiction `(15)`–`(17)` is ALSO already Lean

Fifth search, fifth pre-existing asset:

```text
criticalSource_dvd_exponents_of_kummer_relation      (CriticalSourceKummerObstruction)
      every Kummer relation z^r = c · pₘ^a · qₙ^b in the ACTUAL critical source field forces
      r ∣ a and r ∣ b
criticalSource_not_exists_kummer_relation
      ** hence no nontrivial exponent pair mod r occurs — this is exactly (15)–(17) of §4,
         for the actual source field, with the ground-field constant allowed **
```

So §4's endgame is complete: given a Kummer relation coming from a nontrivial block, the
contradiction is a one-line application.

### The single remaining gap, stated exactly

Everything on this card is now Lean except the passage

```text
a nontrivial block of the monodromy action
  ⟹  an intermediate field of J/O, unramified over the chart at every height-one prime   (E1, E3)
  ⟹  after the torus base change, an intermediate field of the CYCLIC O' = O(c^{1/L})     (E4, E5)
  ⟹  a Kummer relation z^r = c · pₘ^a · qₙ^b with (a,b) ≢ 0 mod r                          (E6)
```

whose last line is killed by `criticalSource_not_exists_kummer_relation` and whose `E5` is
`rank_eq_one_of_isUnit_discr_mvPolynomial`.  Equivalently, in the better packaging, this is the
single statement `(G)` "the monodromy is generated by transpositions", consumed by
`criticalGeometricMonodromy_eq_top_of_generated_by_swaps`.

The formal content of that passage is the **ramification comparison for the chart**: a place of the
chart ring at which the Jacobian is a unit is unramified in `J`.  The tree owns the Jacobian/Schur
identity (`criticalSourceReciprocalJacobian_det_eq_schurRamification`) and the DVR
(`CriticalSchurValuationDVR`), and `Mathlib/RingTheory/DedekindDomain/Different.lean` supplies
`differentIdeal` and `aeval_derivative_mem_differentIdeal`.  That comparison is the one genuinely
missing module, and it delivers `E1`, `E3` and — through `|I| = e` — also `(R)`.

## The one missing module, fully specified: the different at the Schur place

mathlib supplies the whole ramification dictionary in
`Mathlib/RingTheory/DedekindDomain/Different.lean`:

```text
dvd_differentIdeal_iff      P ∣ differentIdeal A B  ↔  ¬ Algebra.IsUnramifiedAt A P
not_dvd_differentIdeal_iff  the negation
conductor_mul_differentIdeal   conductor A θ * 𝔇 = span {aeval θ (derivative (minpoly A θ))}
aeval_derivative_mem_differentIdeal
pow_sub_one_dvd_differentIdeal   P^(e−1) ∣ 𝔇
```

So the missing module is exactly:

```text
LOCAL MONOGENICITY AT THE SCHUR PLACE  ⟹  𝔇 = (Jacobian)  ⟹  ramified iff Jacobian ∈ P
```

concretely

```text
1. B_P = A_p[θ] at the Schur place.  Use ArtinianLocalMonogenic.
       exists_adjoin_eq_top_of_principal_nilpotent
   — a local algebra with principal nilpotent maximal ideal and separable residue field is
   generated by one element.  **Do NOT use CriticalSourcePrimitiveGenerator: it assumes
   criticalGeometricMonodromy = ⊤ and would be circular.**
2. conductor = ⊤ there, so conductor_mul_differentIdeal gives 𝔇 = span {p'(θ)}.
3. p'(θ) is the reciprocal Jacobian determinant up to a unit
       criticalSourceReciprocalJacobian_det_eq_schurRamification
   whose divisorial order is exactly one
       addVal_criticalSchurJacobianDetElement_eq_one .
4. Hence P ∣ 𝔇, so dvd_differentIdeal_iff gives ramified, so e ≥ 2:  **(R)**,
   and via natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn, |I| = e = 2.
5. At any other height-one place of the chart the Jacobian is a unit, so 𝔇 is trivial there and
   not_dvd_differentIdeal_iff gives unramified:  **E1**, hence **E3**.
```

With `(R)`, `E1`, `E3` in hand, `E4` is the torus transfer, `E5` is
`rank_eq_one_of_isUnit_discr_mvPolynomial`, `E6` is
`criticalSource_not_exists_kummer_relation`, and `(4)` closes through either
`criticalGeometricMonodromy_eq_top_of_generated_by_swaps` or the primitivity packaging.

**This is the complete remaining specification of the card.**  Every other ingredient named above is
already an unconditional theorem in the tree.

## Lean progress — `(R)` in sharp form: a different of order one is a simple fold

Sixth and seventh pre-existing assets found: `DifferentIdealMonogenic` (the different of a monogenic
extension is `span {p'(θ)}`) and `DifferentExponentTame.differentIdeal_eq_span_pow` (the tame
different is `P^(e-1)`).  Chaining them with the valuation comparison already in the same file gives
`HTGeometry/DifferentOrderOneSimpleFold.lean` (wired, built):

```text
ramificationIndex_eq_two_of_different_addVal_one
    ** differentIdeal A B = span {J}  and  addVal B J = 1   ⟹   e = 2 **
```

This is `(R)` in its sharp form — not merely `e ≥ 2` but `e = 2`, i.e. a simple fold — and through
`natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn` it gives `|I| = 2`, which is exactly
the input of `exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two_of_card`.

What remains for `(R)` is the **instantiation** at the Schur place: supply the hypotheses of
`ramificationIndex_eq_two_of_different_addVal_one` for the actual Schur DVR pair with `J` the
reciprocal Jacobian determinant.  `addVal B J = 1` is already
`addVal_criticalSchurJacobianDetElement_eq_one`; `differentIdeal = span {J}` is
`differentIdeal_eq_span_aeval_derivative` composed with
`criticalSourceReciprocalJacobian_det_eq_schurRamification`; the local monogenicity and residue
hypotheses come from `ArtinianLocalMonogenic` and `MinpolyDegreeUniformizer` (**not** from
`CriticalSourcePrimitiveGenerator`, which assumes `criticalGeometricMonodromy = ⊤`).

Running tally of assets that already existed and were nearly rebuilt: `|I| = e`; the
`t^L`-invertibility division; §2 and §3 wholesale; the transposition-generation endgame; §4's Kummer
contradiction; the monogenic different; the tame different exponent.  **Search the corpus before
writing anything on this card — the hit rate is above eighty percent.**

### The instantiation of `(R)`: what is present, and the one obstruction

Present in `CriticalSchurIntegralClosurePlace`, so the different of the Schur pair is already
well-formed:

```text
IsDedekindDomain (CriticalSchurNormalIntegralClosure K hm hn)
Module.Finite (CriticalSchurNormalBaseRing) (CriticalSchurNormalIntegralClosure)
IsIntegralClosure.isFractionRing_of_finite_extension
```

so `differentIdeal (CriticalSchurNormalBaseRing …) (CriticalSchurNormalIntegralClosure …)` typechecks
and `dvd_differentIdeal_iff` applies to the Schur prime `P`.

The obstruction is **global versus local monogenicity**:

```text
aeval_derivative_mem_differentIdeal   needs only  Algebra.adjoin K {θ} = ⊤   (field generation)
      gives  p'(θ) ∈ 𝔇        — NOT enough, since P ∣ 𝔇 means 𝔇 ⊆ P
conductor_mul_differentIdeal         needs  conductor A θ = ⊤   (B = A[θ] GLOBALLY)
      gives  𝔇 = span {p'(θ)}  — enough, but global monogenicity of the integral closure is not
                                  available and must not be taken from
                                  CriticalSourcePrimitiveGenerator (circular)
```

Two ways out, either of which closes `(R)`:

```text
(a) localize at the Schur prime first: at a DVR the residue extension is trivial (K is
    algebraically closed), so ArtinianLocalMonogenic gives B_P = A_p[θ] and hence conductor = ⊤
    there; then either dvd_differentIdeal_iff or, better,
    DifferentOrderOneSimpleFold.ramificationIndex_eq_two_of_different_addVal_one gives e = 2
    outright.  This needs "differentIdeal commutes with localization", which mathlib may or may
    not carry — CHECK FIRST.
(b) prove conductor = ⊤ globally for the Schur pair directly from the uniformizer presentation
    (`adjoin_singleton_eq_top` in DifferentExponentTame is exactly this shape and is already
    proved for the DVR case).
```

Route (a) with `DifferentOrderOneSimpleFold` is preferred: it yields `e = 2` on the nose, hence
`|I| = 2`, hence the swap criterion needs only the collision bound `(D)`.

## Lean progress — `E1` is PROVED: the branch locus is contained in the Jacobian divisor

Two modules landed and built.

```text
HTGeometry/RamificationIndexTwoFromDerivative.lean
    mem_pow_sub_one_aeval_derivative                p'(x) ∈ Q^(e-1)
    ramificationIdx_eq_two_of_derivative_uniformizer
        ** p'(x) ∈ Q, ∉ Q², ∉ Q^e  ⟹  e = 2 **
HTGeometry/UnramifiedAwayFromDerivative.lean
    differentIdeal_dvd_span_aeval_derivative        𝔇 ∣ (p'(x))
    isUnramifiedAt_of_aeval_derivative_notMem
        ** p'(x) ∉ P  ⟹  P is unramified over the base   =  E1 **
    aeval_derivative_mem_of_not_isUnramifiedAt      the contrapositive
```

Both need only that `x` generates the extension of fraction fields — no monogenicity of the
integral closure, no conductor computation, no localization of the different.  The obstruction
recorded in the previous section is therefore removed: `dvd_differentIdeal_iff` supplies the
"ramified ⟺ divides the different" direction, and `aeval_derivative_mem_differentIdeal` supplies
`𝔇 ∣ (p'(x))` for free.

### Correction — `(D)` is NOT wiring, and the reason is a count

Re-reading the collision criterion against §3 shows the earlier reading of `(D)` was too
optimistic.  `criticalFibre_eq_of_shared_coprime_tangent` proves *two states with the same coprime
tangent are equal*; that gives at most one **ramified point** of the reduced fibre.  But

```text
|collisionSupport| = Σ_{Q ramified above the Schur place} e_Q · f_Q
```

so `collisionSupport ≤ 2` needs, beyond §3's uniqueness, both `e = 2` and `f = 1` at that point.
Three sheets with one reduction is not excluded by any tangent argument — three points of a line
are still collinear — so a genuine count is unavoidable.  This is recorded so that no session
re-attempts `(D)` as pure wiring.

### The count, and why it is elementary after all

Let `x` be a primitive element of the source over the observation field, `p` its minimal
polynomial, and `x_σ = σ(x)` for the `D` sheets `σ`, all integral at the Schur place `w` of the
normal closure.  Then

```text
p'(x_σ) = Π_{τ ≠ σ} (x_σ − x_τ)                     Splits.eval_root_derivative  (mathlib)
```

Two sheets collide after reduction exactly when `w(x_σ − x_τ) > 0`, and a single such factor
already makes `w(p'(x_σ)) > 0`.  Hence

```text
|collisionSupport| ≤ #{σ : w(p'(x_σ)) ≠ 0} ≤ Σ_σ w(p'(x_σ)) = w(Π_σ p'(x_σ)) = w(disc p) .
```

So `(D)` reduces to the single scalar statement `w(disc p) ≤ 2`, which is
`addVal_criticalSchurJacobianDetElement_eq_one` (source divisorial order one) transported through
`e(w / source Schur place)`.  No fibre-by-fibre decomposition of the geometric fibre into primes is
needed, and neither `f = 1` nor §3 is needed separately: the discriminant bound subsumes both.

This is the route to build.  The general half is a DVR statement about split polynomials, with no
reference to the horizon at all.

## The exact obstruction to `(R)`+`(D)`, and the mathlib gap that closes it

Chasing the count to the end shows the two obligations are one, and that neither the different nor
the discriminant can settle it alone.  Write `A` for the observation Schur DVR, `B` for the
integral closure of `A` in the source, `Q₀` for the Schur prime of `B`, `W` for the integral closure
in the normal closure, `w` for the chosen place of `W`, `I` for its inertia group, and

```text
t := e(w / Q₀) ,     e(Q₀ / A) = 2 ,     |I| = e(w / A) = 2t .
```

The corpus owns `v_{Q₀}(𝔇_{B/A}) = 1` (`addVal_criticalSchurJacobianDetElement_eq_one`), and
mathlib owns transitivity of the different
(`differentIdeal_eq_differentIdeal_mul_differentIdeal`).  Combining them gives

```text
w(𝔇_{W/A}) = w(𝔇_{W/B}) + t = (t − 1) + t = 2t − 1 = |I| − 1 ,
```

an identity for **every** `t`.  So the different is exactly uninformative about `t`, and so is the
discriminant, which is its norm.  Neither §3 nor a tangent argument helps: three sheets sharing a
reduction is a statement about `e`, not about tangents.

**What does settle it is that tame inertia is cyclic.**  `I` acts faithfully on the sheets
(`criticalSchurInertiaAction_injective`, already Lean) and every `I`-orbit lies inside one fibre of
the reduction (`criticalSchurInertia_residue_smul`, already Lean), whose size is bounded by
`1 + t` through the derivative count
(`RootCongruenceValuationCount.addVal_eval_derivative_ne_zero_of_root_congruent`).  If `I` is
cyclic, its subgroups are totally ordered, so the faithfulness forces some point to have trivial
stabiliser, i.e. an orbit of full size `|I| = 2t`.  Then

```text
2t ≤ 1 + t   ⟹   t = 1   ⟹   |I| = 2   and   |collisionSupport| ≤ 2 .
```

That is `(R)` and `(D)` at once.

### The mathlib gap, and an elementary quotient-free proof

`Mathlib/RingTheory/Valuation/RamificationGroup.lean` defines only the decomposition and inertia
subgroups; higher ramification groups are an explicit `TODO`, and "tame inertia is cyclic" is
absent.  The corpus does not have it either.  The usual proof runs through the filtration
`G_i / G_{i+1} ↪ k⁺`; the following avoids the filtration entirely.

Let `π` be a uniformizer, `g` an automorphism of finite order `N` acting trivially on the residue
field, and suppose `v(g π − π) ≥ 2`.  Every `g^j` then also satisfies `v(g^j π − π) ≥ 2` (induction,
using that an automorphism preserves `v`), so with `gπ − π = c π^i`, `i = v(gπ−π)`, `c` a unit,

```text
g^j (c π^i) = (g^j c) (g^j π)^i ≡ c π^i        (mod π^{i+1})
g^N π − π = Σ_{j<N} g^j (g π − π) ≡ N · c π^i  (mod π^{i+1})
```

and `g^N = 1` forces `N c ∈ 𝔪`, hence `N ∈ 𝔪` — impossible when the residue field has
characteristic zero.  So `g π = π`, the ratio character `g ↦ (g π)/π mod 𝔪` is injective into
`k^×`, and a finite subgroup of `k^×` is cyclic.

Residual triviality also gives `W = A[π]` (`UniformizerPowerBasis.uniformizerPowBasis`), which turns
`g π = π` into `g = 1`, closing the injectivity.  The whole argument is elementary and belongs in
`HTGeometry` as a general theorem, independent of the horizon.

## Correction — cyclicity is used through "unique subgroup of each order", not through ordering

The previous section justified `t = 1` by "subgroups of a cyclic group are totally ordered".  That
is false: `ℤ/6` has subgroups of orders `2` and `3` with trivial intersection, and it acts
faithfully on `2 + 3` points with no free orbit.  The correct use of cyclicity is different, and
sharper.

Write `Stab(σ) = I ∩ σHσ^{-1}` for the stabiliser of a sheet.  Faithfulness of the inertia action
(`criticalSchurInertiaAction_injective`) says `⋂_σ Stab(σ) = 1`, since the kernel of the action of
`I` on `G/H` is `I ∩ core(H)`.  Now:

* a sheet over an unramified prime has `Stab(σ) = I`;
* a sheet over the Schur prime has `|Stab(σ)| = e(w / Q₀) = t`.

In a **cyclic** group there is exactly one subgroup of each order, so all the stabilisers of the
second kind coincide — conjugation by the decomposition group preserves order, hence fixes the
subgroup.  Therefore `⋂_σ Stab(σ)` is that single subgroup of order `t`, and faithfulness gives
`t = 1`.  Equivalently: every stabiliser has index `1` or `2` in `I`, so every stabiliser contains
the unique subgroup of index two, which must then be trivial.

### What is genuinely irreducible: `f_{Q₀} = 1`

A separate check settles what the different and the discriminant can and cannot see.  With `α`
generating the source order over the observation Schur DVR,

```text
v_A(disc) = v_A(N_{S/O}(p'(α))) = Σ_Q f_Q · v_Q(𝔇_{B/A}) = f_{Q₀} · 1 = f_{Q₀}
```

while the conductor–discriminant identity reads `Σ_Q f_Q (e_Q − 1) = v_A(disc)`, i.e.
`f_{Q₀} = f_{Q₀}`.  So no amount of different or discriminant bookkeeping constrains `f_{Q₀}`: the
residue degree of the Schur place over the branch place is **irreducible extra content**, and it is
exactly the card's sentence "the Schur divisor maps 1–1 to the branch".

That content is §3, and §3 alone: `criticalFibre_eq_of_shared_coprime_tangent` applied over the
residue field of the *upper* Schur place says all colliding sheets carry one and the same reduced
state, which forces both "one ramified prime" and `f_{Q₀} = 1` at once — `f_{Q₀}` distinct residue
embeddings would produce `f_{Q₀}` distinct ramified reduced states.

**Corrected division of labour.**

```text
f_{Q₀} = 1 and a unique ramified prime      §3, wiring of existing lemmas        (D) part 1
e_{Q₀} = 2                                  Jacobian order one + tameness        (R)
|collisionSupport| = e·f = 2                orbit/prime correspondence           (D) part 2
```

and the tame-inertia development below is what makes the last line usable, by pinning `e(w/Q₀) = 1`
so that the upper place does not multiply the count.

## Lean progress — TAME INERTIA IS CYCLIC, and the collision bound it powers

Three more modules, all built, all with narrow imports (each under two seconds).

```text
HTGeometry/TameInertiaRigidity.lean
    addVal_smul                                   an automorphism preserves the valuation
    dvd_of_mem_maximalIdeal, dvd_smul_self
    sq_dvd_smul_pow_sub                           the second-order condition passes to powers
    smul_uniformizer_eq_self_of_sq_dvd
        ** π² ∣ gπ − π  ⟹  gπ = π **              (no wild inertia in residue char 0)
    smul_eq_self_of_smul_uniformizer_eq_self
        ** gπ = π  ⟹  g is the identity **        (tame rigidity)

HTGeometry/TameInertiaCyclic.lean
    ratioElt, smul_eq_mul_ratioElt, ratioElt_unique, isUnit_ratioElt
    ratioElt_mul                                  ratioElt π (gh) = ratioElt π g · g·ratioElt π h
    residueRatioHom : Γ →* ResidueField W         the tame ratio character
    residueRatioHom_injective
    isCyclic_of_tame
        ** a finite group acting faithfully on a DVR by ring automorphisms, trivially on a
           residue field of characteristic zero, is CYCLIC **

HTGeometry/CyclicCollisionOrderBound.lean
    exists_eq_of_ncard_le_two
    sq_smul_eq_self_of_fibre_le_two               every square acts trivially
    natCard_le_two_of_isCyclic
        ** faithful + cyclic + fibres of size ≤ 2  ⟹  the group has ≤ 2 elements **
```

`Mathlib/RingTheory/Valuation/RamificationGroup.lean` carries only the decomposition and inertia
subgroups and leaves the higher filtration as a `TODO`, so none of this was available; the corpus
did not have it either.  The proof deliberately avoids the filtration: with `gπ − π = u π^k`,

```text
g^N π − π = Σ_{j<N} g^j (gπ − π) ≡ N · u π^k   (mod π^{k+1})
```

and `g^N = 1` forces `π ∣ N`, impossible in residue characteristic zero.  Every step is a
divisibility — no valuation sums, no quotient groups, no completeness, no Hensel.

**What this buys the card.**  The three inputs of the endgame now read

```text
Γ = criticalSchurInertiaGroup acts on the upper Schur valuation ring    (corpus)
the action is faithful on sheets                criticalSchurInertiaAction_injective   (corpus)
inertia fixes residues                          criticalSchurInertia_residue_smul      (corpus)
inertia is therefore cyclic                     isCyclic_of_tame                       (NEW)
reduction fibres have ≤ 2 members               root-congruence count + §3             (open)
|I| ≤ 2, hence a transposition                  natCard_le_two_of_isCyclic             (NEW)
```

so the single remaining mathematical obligation on this card is the middle line of the last block:
that each fibre of `criticalGeometricSheetToSchurReducedFibre` has at most two members.

## Lean progress — the collision tangent, and corank one at the residue field

Two more modules, built.

```text
HTGeometry/CriticalFibreCollisionTangent.lean
    exists_coeff_ne_zero, mem_maximalIdeal_of_irreducible
    exists_not_C_pow_dvd
    exists_maximal_C_pow_dvd_pair          the common uniformizer power of a polynomial pair
    X_pow_dvd_of_C_mul                     cancel a nonzero constant from a horizon divisibility
    map_residue_eq_zero_iff
    exists_reduced_tangent_of_congruent
        ** two distinct points of one critical fibre over a DVR agreeing modulo the maximal
           ideal give a NONZERO low tangent pair over the residue field, satisfying the
           linearized compatibility relation at the reduced point **

HTGeometry/SquareMatrixCorankOne.lean
    finrank_ker_mulVecLin_eq_one_of_det_eq_zero
    finrank_ker_mulVecLin_map_eq_one
        ** det = 0 with one surviving cofactor  ⟹  corank one over EVERY extension field **
```

The first is §3's missing bridge: a collision at the special fibre *is* a vertical tangent at the
reduced point, which is exactly what `criticalFibre_eq_of_shared_coprime_tangent` consumes.  The
proof subtracts the two compatibility relations,

```text
X^(m+n) ∣ D (p₂ + Q) + (p₁ + P) E + D E ,
```

divides by the largest common power of a uniformizer — which kills the quadratic term, since the
common power is at least one — and reduces.

The second removes the mismatch of fields.  Generic corank one
(`finrank_ker_criticalSchurGenericMatrix_eq_one`) lives on the function field of the Schur divisor,
while a collision tangent lives in the residue field of the *upper* Schur place.  Both of its
hypotheses are determinantal, so they transport along the field map, and the corank stays one where
the tangent actually is.  The proof pattern is the one already used for the generic statement,
extracted as a general theorem so no session re-derives it.

### What remains, stated exactly

```text
(D1) all collision tangents lie in the kernel of the base-changed Schur matrix    corpus wiring
(D2) hence any two are proportional; isCoprime_of_low_tangent_unique gives coprimality
(D3) criticalFibre_eq_of_shared_coprime_tangent  ⟹  ONE non-singleton reduction fibre
(D4) that fibre has ≤ 2 members                  root count + tame rigidity
(P)  §4 steps 4a–4b: block system, block cover of the torus chart
```

`(D4)` is where the tame-inertia modules pay: with `(D3)` the unique non-singleton fibre is a single
inertia orbit, cyclicity makes its stabiliser normal, faithfulness makes it trivial, and the
root-congruence count then bounds the fibre by `1 + v(𝔇) = 2`.

## Lean progress — the tangent is a kernel vector, and the conormal obstructs lifting

Three more modules, all built.

```text
HTGeometry/FaithfulSingleOrbitFree.lean
    eq_one_of_forall_smul_eq
    eq_one_of_smul_eq_of_unique_nontrivial_orbit
        ** one nontrivial orbit + commutative + faithful ⟹ that orbit is FREE **
    natCard_orbit_eq_natCard_of_free

HTGeometry/LowTangentJacobianKernel.lean
    dvd_reciprocal_of_low_tangent            V ≡ -Y²U to the horizon
    jacobian_mulVec_eq_zero_of_low_tangent
        ** a low tangent IS a kernel vector of criticalReciprocalJacobian **
    coeff_vec_ne_zero
    low_tangent_unique_of_finrank_ker_eq_one
        ** corank one ⟹ any two low tangents have proportional raw components **

HTGeometry/ConormalLiftObstruction.lean
    dvd_of_mul_reciprocal, coeff_mul_eq_zero_of_low
    conormal_eq_zero_of_lifts
        ** a liftable observation deformation is killed by the conormal of the tangent **
```

`LowTangentJacobianKernel` closes the gap between generic corank one and coprimality: its last
theorem is precisely the uniqueness hypothesis of `isCoprime_of_low_tangent_unique`.  The proof is
the identity `V ≡ -Y²U`, obtained by multiplying the tangent relation by `Y` and using `AY ≡ 1`;
since `V` has degree below `n`, the coefficients of `-Y²U` in degrees `n … n+m-1` vanish, and those
are the rows of the Jacobian.

`ConormalLiftObstruction` supplies §2's missing half.  It shows the conormal functional of the
tangent annihilates every liftable deformation — it *is* the first-order equation of the branch.
The proof multiplies the lifting relation by `V`, substitutes `AV ≡ -UY`, cancels the invertible
`Y`, and reads the coefficient at `m+n-1`, where the low-times-low term cannot contribute.

### The remaining step, stated exactly

Two ramified states over one observation have conormals `λ_p`, `λ_q`, each annihilating its own
liftable deformations.  What is still needed is that these two hyperplanes coincide:

```text
(C1) lift_p = ker λ_p          dimension count: corank one gives dim (im T) = L-1,
                               and exists_conormal_ne_zero gives λ_p ≠ 0
(C2) lift_p = lift_q           both equal the tangent hyperplane of the irreducible Schur
                               divisor at its generic point
```

`(C2)` is where the irreducibility of the Schur divisor (`criticalSchurTailIdeal_isPrime`, already
Lean) enters: at a generic — hence smooth — point of an irreducible divisor there is a single
tangent hyperplane, so two conormals through it are proportional.  With that,
`conormal_determines_tangent_smul` scales the two tangents to the same `(U, V)`, and
`criticalFibre_eq_of_shared_coprime_tangent` finishes §3.

## The definitive route map for `(R)` and `(D)`, after exhausting the local theory

`RootCongruenceValuationCount` was rewritten with narrow imports (build time 427s → 2.4s) and
strengthened to the sharp count

```text
card_congruent_roots_le_addVal_eval_derivative
    ** #{roots congruent to x} ≤ v(f'(x)) **
```

so a collision class of size `k` forces the derivative to vanish to order at least `k - 1`.  With
that in hand the whole of `(R)` and `(D)` collapses to ONE scalar.  Let `A` be the observation Schur
DVR, `B` the integral closure of `A` in the source, `α` a local generator (which exists:
`DedekindOrderMonogenic.exists_adjoin_eq_top_of_dedekind_finite`), and `p = minpoly_A α`.  Then

```text
D - #(distinct reductions) = Σ_Q f_Q (e_Q - 1) = v_A(disc p) = v_A(N_{S/O}(p'(α)))
```

and a single non-singleton reduction fibre of size `2` is exactly `v_A(disc p) = 1`.  Therefore

```text
v_A(disc p) = 1   ⟹   one ramified prime, e = 2, f = 1, |collisionSupport| = 2
              ⟹   (R) and (D) together.
```

**What the corpus supplies, and what it does not.**  `addVal_criticalSchurJacobianDetElement_eq_one`
gives `v_{Q₀}(Jac) = 1` — the order of the Jacobian at the *source* Schur place.  Passing to
`v_A(disc)` needs both of

```text
(i)  (Jac) = 𝔇_{B/A}      "the different of a complete intersection is the Jacobian ideal"
(ii) f_{Q₀} = 1           "the Schur divisor maps 1-1 to the branch"      = §3
```

and `v_A(N(Jac)) = Σ_Q f_Q v_Q(Jac) = f_{Q₀}` shows that `(ii)` is *not* implied by any amount of
ramification bookkeeping — it is the irreducible geometric content, exactly as the card's §3 says.

**A negative result, so that no session repeats the search.**  The tame different formula
(`DifferentExponentTame.addVal_generator_differentIdeal`, corpus) does not shortcut this: it needs a
*generator of the different* as input, and its residue hypothesis `hres` is `f = 1` itself.  Corank
one does not shortcut it either: corank one holds at a cusp, so it bounds the embedding dimension of
the collision class but not its length; the length is second-order data, and the second-order datum
is precisely `v(Jac) = 1`.

**Both remaining items are general theorems worth having on their own.**  `(i)` is a mathlib gap —
`Mathlib/RingTheory/DedekindDomain/Different.lean` carries only the monogenic case
(`conductor_mul_differentIdeal`), and there is no Fitting-ideal or Kähler bridge in either mathlib
or this corpus beyond the monogenic normal form
(`ConstraintRelativity.MonogenicKaehler.annihilator_kaehler`) and the principal-symbol identity
(`GeneralKaehlerPrincipalSymbol.polynomialKaehlerCoefficientIdeal_eq_jacobianMinorIdeal`).  Those
two are the ends of the bridge; the middle — `𝔇 = Fitting₀(Ω_{B/A})` for a finite flat
complete intersection — is what must be built.

## Correction — one half of the Jacobian–different bridge is ALREADY in the tree

A further search (the ninth time the corpus turned out to own what looked missing) finds

```text
HTGeometry/JacobianKaehlerAnnihilator.lean
    LinearMap.det_smul_mem_range          the determinant of an endomorphism kills its cokernel
    repr_cotangentComplex_relationCotangent
        the presentation differential is the coordinate matrix of the cotangent-complex map
    jacobian_smul_kaehler_eq_zero
        ** for a square presentation with identity relation-to-variable matching, the presentation
           Jacobian annihilates every relative Kähler differential **
```

with *no* regular-sequence, smoothness, domain or finiteness hypothesis.  It is stated over
mathlib's `Algebra.PreSubmersivePresentation`, so `(Jac) ⊆ Ann(Ω) = 𝔇` is done.  My
`SquareMatrixCokernelAnnihilator` is the matrix-level twin of its first lemma; it is kept because
the corank-one theorem below is stated for matrices, but no session should build either again.

**So only the reverse inclusion was ever missing**, and that is exactly what corank one supplies:
over a discrete valuation ring, Smith normal form (`SmithNormalFormDVR.exists_smithNormalForm`,
also already in the tree) makes the elementary divisors a divisibility chain, corank one of the
reduction leaves exactly one non-unit among them, and then

```text
Ann (coker M) = (largest elementary divisor) = (det M) .
```

Reading that at the Schur place gives `𝔇 = (Jac)`, hence `v(𝔇) = v(Jac) = 1`, hence — through the
already-landed `ramificationIdx_eq_two_of_derivative_uniformizer` — `e = 2`, which is `(R)`.

The one step still to write for that chain is `Ω ≅ coker (Jacobian matrix)`, which follows from
mathlib's `Algebra.Extension.exact_cotangentComplex_toKaehler` together with the corpus's
`repr_cotangentComplex_relationCotangent` and surjectivity of `relationCotangent`: exactness gives
`Ω = coker (cotangentComplex)`, and the relations generate the conormal module, so the range of the
cotangent complex is the range of the Jacobian matrix.

## Lean progress — the reverse inclusion of the Jacobian–different bridge is PROVED

```text
HTGeometry/CorankOneCokernelDeterminant.lean          (built)
    mem_range_diagonal_mulVecLin_iff, mem_annihilator_coker_diagonal_iff
    prod_associated_of_unique_nonunit, annihilator_coker_diagonal_eq_span_det
    mulVec_left_cancel, mem_annihilator_coker_iff, annihilator_coker_eq_of_unit_equiv
    residue_eq_zero_iff_not_isUnit
    annihilator_coker_eq_span_det_of_corank_one
        ** over a DVR, corank one of the reduction ⟹ Ann (coker M) = (det M) **
```

Together with the corpus's `jacobian_smul_kaehler_eq_zero` (the forward inclusion) this is the
complete statement "the different of a square presentation is the Jacobian ideal", at any place
where the reduced Jacobian has corank one.  The proof uses three things the tree already owned —
`SmithNormalFormDVR.exists_smithNormalForm`, `Matrix.rank_diagonal`, and the divisibility chain —
so the only genuinely new content is the diagonal annihilator and the invariance of the annihilator
under equivalence of matrices.

### The `(R)` route, now fully explicit

```text
(a) Ω ≅ coker (Jacobian matrix)     mathlib exact_cotangentComplex_toKaehler + surjectivity of
                                    relationCotangent, which is three lines from mathlib's
                                    Extension.Cotangent.span_eq_top_of_span_eq_ker
(b) the critical fibre as a PreSubmersivePresentation over the observation Schur DVR
(c) that presentation's Jacobian = criticalReciprocalJacobian
(d) corank one at the Schur place   corpus, transported by SquareMatrixCorankOne
(e) v(Jac) = 1                      corpus ✓
⟹  𝔇 = (Jac),  v(𝔇) = 1,  e = 2  =  (R)
```

`(b)` is the remaining construction and its shape is concrete: `m + n` variables
`a_0 … a_{m-1}, b_0 … b_{n-1}`, and `m + n` relations `f_k` = the coefficient of `X^k` in
`(A + P)(B + Q) - 1`, which is square as `PreSubmersivePresentation` requires.  Its Jacobian is the
Sylvester-type block matrix `[T(Y) | T(A)]`, whose determinant reduces by Schur complement to the
`m × m` `criticalReciprocalJacobian` already in the tree — the elimination of `b`, which is
determined by `a` through `B ≡ A⁻¹`.

## Lean progress — the Jacobian–different bridge is CLOSED

```text
HTGeometry/CotangentPresentationCokernel.lean
    relationCotangent_surjective        the relations generate the conormal module
    cotangentSpaceEquiv, cotangentSpaceEquiv_cotangentComplex
    map_range_cotangentComplex          range(cotangentComplex) ↦ range(aevalDifferential)
    annihilator_eq_of_linearEquiv
    kaehlerEquivCoker                   Ω[S⁄R] ≃ₗ (ι → S) ⧸ range(aevalDifferential)
    annihilator_kaehler_eq_span_jacobian
        ** over a DVR, with the reduced Jacobian of corank one,
           Ann (Ω[S⁄R]) = (P.jacobian) **
```

With `JacobianKaehlerAnnihilator.jacobian_smul_kaehler_eq_zero` (already in the tree) supplying the
forward containment, the different of a square presentation is now *exactly* the Jacobian ideal at
any place where the reduced Jacobian has corank one.  Two mathlib facts made the proof short:
`Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker` (the relations span the conormal module)
and `Algebra.Extension.exact_cotangentComplex_toKaehler`.

Step `(a)` of the `(R)` route is therefore done, and `(R)` is now purely corpus-side:

```text
(b) the critical fibre as a PreSubmersivePresentation over the observation Schur DVR
(c) that presentation's Jacobian = criticalReciprocalJacobian
(d) corank one at the Schur place, transported by SquareMatrixCorankOne
(e) v(Jac) = 1                                                              corpus ✓
```

`(b)` is the construction to write next: `m + n` variables `a_0 … a_{m-1}, b_0 … b_{n-1}` and the
`m + n` relations `f_k = [X^k] ((A + P)(B + Q) - 1)`, square as `PreSubmersivePresentation`
requires, whose Jacobian is the Sylvester block `[T(Y) | T(A)]`.  Its Schur complement — eliminating
`b`, which `B ≡ A⁻¹` determines from `a` — is the `m × m` `criticalReciprocalJacobian` the tree
already carries, which is what `(c)` has to prove.

## Lean progress — steps `(a)` and `(b)` of `(R)` are DONE, and `(c)`'s differential is computed

```text
HTGeometry/CotangentPresentationCokernel.lean     (built)
    annihilator_kaehler_eq_span_jacobian
        ** over a DVR with the reduced Jacobian of corank one, Ann (Ω[S⁄R]) = (P.jacobian) **

HTGeometry/HorizonFibrePresentation.lean          (built)
    horizonRawCoeff, horizonRecipCoeff, horizonRelation, horizonFibreAlgebra
    horizonPresentation
        ** the critical fibre as a SQUARE PreSubmersivePresentation, with map = id **

HTGeometry/HorizonPresentationDifferential.lean
    pderiv_horizonRelation_rawVar      ∂ f_k / ∂ a_{i₀} = Y_{k-i₀}   (i₀ ≤ k), else 0
    pderiv_horizonRelation_recipVar    ∂ f_k / ∂ b_{j₀} = A_{k-j₀}   (j₀ ≤ k), else 0
```

`(b)` was far cheaper than expected: mathlib's `Algebra.Presentation.naive` presents
`R[X_σ] ⧸ span (range v)` directly, so the critical fibre presentation is a definition, not a
construction.  And `map = id` is exactly the hypothesis both bridge theorems consume.

The differential is therefore the Sylvester block `[T(Y) | T(A)]`, as predicted.  What remains of
`(c)` is one matrix identity:

```text
T_Y^full · [T(Y) | T(A)] = [ first m columns of T(Y²) | e_0 … e_{n-1} ]
```

because `T_Y^full` is the inverse of `T_A^full` (as `A Y ≡ 1` to the horizon) and has unit
determinant.  Laplace expansion along the identity columns then leaves exactly
`det (rectangularSchurToeplitz (Y²) n m)` — the corpus's `criticalReciprocalJacobian`, up to sign.
That is `(c)`; `(d)` transports corank one to the Schur place through `SquareMatrixCorankOne`.

## Lean progress — step `(c)` of `(R)` is CLOSED

Seven modules, all built, chain into the identification of the abstract presentation Jacobian with
the concrete Schur equation:

```text
HTGeometry/HorizonPresentationDifferential.lean
    ∂ f_k / ∂ a_{i₀} = Y_{k-i₀},   ∂ f_k / ∂ b_{j₀} = A_{k-j₀}
HTGeometry/HorizonCompletedJets.lean
    horizonRelation k = (rawJet * recipJet - 1).coeff k
HTGeometry/HorizonFibreJetInverse.lean
    X^(m+n) ∣ rawJetFibre * recipJetFibre - 1
HTGeometry/TruncatedToeplitz.lean
    toeplitz_mul, det_toeplitz, toeplitz_mul_toeplitz_of_inverse
HTGeometry/IdentityCornerDeterminant.lean
    associated_det_of_identity_columns
HTGeometry/HorizonSylvesterDifferential.lean
    transpose_toMatrix'_aevalDifferential      differentialᵀ = [ T(Y) | T(A) ]
HTGeometry/HorizonJacobianSchurDeterminant.lean
    toeplitz_mul_horizonSylvester              T(Y) · [ T(Y) | T(A) ] = [ T(Y²) | 1 ]
    associated_jacobian_rectangularSchurToeplitz
        ** the presentation Jacobian is ASSOCIATED to
           det (rectangularSchurToeplitz ((Y·Y).coeff) n m) **
```

The Toeplitz calculus is what makes this elementary: `T(F) T(G) = T(F G)` turns the fibre relation
`A Y ≡ 1` into a literal matrix inverse, with no completion and no limits, so the raw block of the
Sylvester matrix becomes an identity corner and the reciprocal block becomes `T(Y²)`.

### Status of `(R)`

```text
(a) Ω ≅ coker (Jacobian), Ann Ω = (jacobian)     CotangentPresentationCokernel      DONE
(b) the critical fibre as a square presentation  HorizonFibrePresentation           DONE
(c) that Jacobian = the Schur determinant        HorizonJacobianSchurDeterminant    DONE
(d) corank one at the Schur place                SquareMatrixCorankOne + corpus     OPEN
(e) v(Jac) = 1                                   corpus                             DONE
```

With `(d)`, `annihilator_kaehler_eq_span_jacobian` gives `𝔇 = (Jac)`, hence `v(𝔇) = 1`, hence
`e = 2` through the already-landed `ramificationIdx_eq_two_of_derivative_uniformizer` — which is
`(R)`.

## The Jacobian–different bridge is OWNED, and what `(d)` still needs

```text
HTGeometry/PresentationDifferentJacobian.lean          (built)
    annihilator_kaehler_eq_span_jacobian_of_det_eq_zero
        ** square presentation over a DVR, reduced Jacobian with det 0 and one surviving
           codimension-one cofactor  ⟹  Ann (Ω[S⁄R]) = (P.jacobian) **
HTGeometry/SquareMatrixCorankOne.lean                  (extended, built)
    rank_add_one_eq_of_det_eq_zero, rank_map_add_one_eq_of_det_eq_zero
        corank one in the rank form the annihilator theorem consumes, and its transport
        along any extension of the coefficient field
```

The hypothesis shape — `det = 0` plus one surviving cofactor — is exactly the pair the corpus
already proves for the Schur matrix (`criticalSchurGenericMatrix_det_eq_zero`,
`criticalSchurGenericMatrix_cornerCofactor_ne_zero`), and `rank_map_add_one_eq_of_det_eq_zero`
carries it from the function field of the Schur divisor to the residue field of the upper place.

**What `(d)` still needs, exactly.**  Two identifications, both corpus-side:

```text
(d1) instantiate horizonPresentation over the observation Schur DVR, and identify
     horizonFibreAlgebra with the localised source order
(d2) Ann (Ω[B⁄A]) = differentIdeal A B for a monogenic extension of Dedekind domains
```

`(d2)` is the last general theorem of the chain.  Note it does **not** need corank one: for a
monogenic presentation the Jacobian matrix is `1 × 1`, the cotangent module is `B ⧸ (p'(x))`, and
the annihilator of a cyclic quotient is its defining ideal
(`ConstraintRelativity.MonogenicKaehler.annihilator_monogenicOmega`, already in the tree, stated for
`AdjoinRoot`).  What has to be supplied is the transport along `B ≃ₐ[A] AdjoinRoot (minpoly A x)`,
which is `AdjoinRoot.minpoly.equivAdjoin` composed with `Subalgebra.topEquiv` under
`Algebra.adjoin A {x} = ⊤`.

With `(d1)` and `(d2)`, `annihilator_kaehler_eq_span_jacobian_of_det_eq_zero` gives `𝔇 = (Jac)`,
`addVal_criticalSchurJacobianDetElement_eq_one` gives `v(𝔇) = 1`, and the already-landed
`ramificationIdx_eq_two_of_derivative_uniformizer` gives `e = 2` — which is `(R)`.

### `(d2)` in detail: what the transport needs, and why it cannot be dodged

`(d2)` is `Ann (Ω[B⁄A]) = differentIdeal A B` for a monogenic extension.  The right-hand side is
`span {p'(x)}` (`DifferentIdealMonogenic.differentIdeal_eq_span_aeval_derivative`), and the
left-hand side is `span {p'(root)}` for `AdjoinRoot (minpoly A x)`
(`ConstraintRelativity.MonogenicKaehler.annihilator_kaehler`).  So the whole content is the
transport along

```text
minpoly.equivAdjoin :  AdjoinRoot (minpoly A x) ≃ₐ[A] adjoin A {x}          (mathlib)
Subalgebra.topEquiv :  adjoin A {x} = ⊤  ⟹  adjoin A {x} ≃ₐ[A] B
```

Two routes were tried and the second is the one to take.

* Redoing the `MonogenicKaehler` construction directly for `B` rather than for `AdjoinRoot` does
  **not** avoid anything: well-definedness of `g(x) ↦ g'(x)` needs exactly that the kernel of
  `A[X] → B` is `(minpoly)`, which is `minpoly.equivAdjoin` again.
* So the transport must be built.  Neither mathlib nor the corpus has "Kähler differentials
  transport along an algebra isomorphism"; it is a general, reusable theorem.  The plumbing point
  learned here: do not put the pulled-back `Module B Ω[C⁄A]` in the *statement* — instead take
  `[Algebra B C]` `[IsScalarTower A B C]` with `algebraMap B C` bijective as hypotheses, so that
  `KaehlerDifferential.map A A B C : Ω[B⁄A] →ₗ[B] Ω[C⁄A]` typechecks with the instance coming from
  the algebra structure rather than from `Module.compHom`.

## Lean progress — `(d2)` is CLOSED, and `(R)`'s mathematical content is now a general theorem

```text
HTGeometry/KaehlerAnnihilatorTransport.lean            (built)
    annihilator_kaehler_map_of_surjective
    annihilator_kaehler_algEquiv
        ** the annihilator of Ω is an isomorphism invariant **
HTGeometry/MonogenicKaehlerAnnihilator.lean            (built)
    monogenicEquiv, monogenicEquiv_mk
    annihilator_kaehler_monogenic       Ann (Ω[B⁄A]) = (p'(x))  for B = A[x]
HTGeometry/JacobianDerivativeOrder.lean                (built)
    span_jacobian_eq_span_aeval_derivative        (P.jacobian) = (p'(x))
    addVal_aeval_derivative_eq_addVal_jacobian    v(p'(x)) = v(P.jacobian)
HTGeometry/DifferentIdealJacobian.lean                 (built)
    differentIdeal_eq_span_jacobian
        ** differentIdeal A B = (P.jacobian) for a square presentation over a DVR whose
           reduced Jacobian has det 0 and one surviving codimension-one cofactor **
```

The transport was the only genuinely missing piece, and it is shorter than expected: **only the
push-forward along a surjection is needed, applied twice — once in each direction of the
isomorphism** — so no injectivity, no inverse Kähler map, and none of the `Module.compHom` plumbing.
The push-forward itself is three lines from `KaehlerDifferential.map_surjective_of_surjective`.

So the mathematical content of `(R)` is now a general theorem: **the divisorial order of the
different is the order of the presentation Jacobian**, hence a Jacobian that is a uniformizer is a
simple fold.

### `(d1)`, and what it really asserts

`(d1)` is not bookkeeping.  It asks for an isomorphism between `horizonFibreAlgebra` — localised at
the Schur point — and the source Schur DVR `criticalSchurSourceValuationSubring`.  That is the
statement that the total space of the critical fibration is **regular at the fold**, i.e. that the
local ring of the fibre algebra there is a discrete valuation ring.  It is the last geometric input
of `(R)`, and it should be attacked through the corank-one datum: a hypersurface singularity of
embedding dimension one whose defining equation has order one is regular.

## A shorter road to `(R)`: `(d1)` is not needed, and the fold condition is not needed either

Two corrections, both of which shrink the remaining work.

**First correction — `(R)` as the card consumes it is only `e ≥ 2`.**  The endgame theorem in the
tree is

```text
criticalGeometricMonodromy_eq_top_of_ramification_of_degree_of_isPreprimitive
    hram  : 2 ≤ Ideal.ramificationIdxIn (maximalIdeal (CriticalSchurNormalBaseRing …)) …
    hdeg  : Nat.card sheets ≤ (range criticalGeometricSheetToSchurReducedFibre).ncard + 1
    hprim : IsPreprimitive …
```

so the sharp form `e = 2` — which is what forced the different, monogenicity, the presentation and
`(d1)` — is *not* what the card needs.  It needs only **ramification**, `e ≥ 2`.  The sharp form
remains a theorem worth having (`DifferentOrderOneSimpleFold`,
`DifferentIdealKaehlerAnnihilator`), but it is not on the critical path.

**Second correction — ramification is the *nonvanishing* of the relative differentials, and that
needs no corank, no reducedness, and no fold condition.**  Over a local base with a discrete
valuation ring upstairs and separable residue extension,

```text
Algebra.FormallyUnramified.of_map_maximalIdeal  (mathlib)
    𝔪_A B = 𝔪_B   ⟹   Ω[B⁄A] = 0
```

so `Ω[B⁄A] ≠ 0` gives `𝔪_A B ≠ 𝔪_B`, hence — a nonzero ideal of a DVR other than the maximal ideal
lies in its square — `𝔪_A B ⊆ 𝔪_B²`, which is `e ≥ 2`.  And `Ω[B⁄A] ≠ 0` is *exactly* the statement
that the coordinate Jacobian is not invertible, which the tree already owns twice over
(`criticalSourceReciprocalJacobian_det_eq_schurRamification`,
`addVal_criticalSchurJacobianDetElement_eq_one`).

Recorded because a whole session was spent on the alternative: the second-order (Morin) fold
condition `⟨dσ, u⟩ ∉ P`, which *is* needed if one insists on computing `e` from valuations of
observation functions, is **not** needed here.  Only `det ∈ 𝔪` is.

### Lean progress — the general half of the new route is CLOSED

```text
HTGeometry/KaehlerRelativeSpan.lean                        (built)
    range_mapBaseChange_eq_span     range (mapBaseChange R A B) = span B {D a | a ∈ A}
    kaehlerQuotientEquiv            Ω[B⁄R] ⧸ span B {D a | a ∈ A}  ≃ₗ[B]  Ω[B⁄A]
    cotangentVanishingSubalgebra    elements with differential in a submodule form a subalgebra
    D_mem_of_adjoin_eq_top          ** differentials of algebra generators suffice **
    D_mem_of_isLocalization         ** differentials of a ring the base localizes suffice **
HTGeometry/KaehlerRamificationCriterion.lean               (built)
    isUnit_det_of_span_eq_top       a spanning family of the right size has unit determinant
    le_maximalIdeal_sq_of_ne        a nonzero non-maximal ideal of a DVR lies in 𝔪²
    map_maximalIdeal_le_sq_of_not_subsingleton
        ** Ω[B⁄A] ≠ 0  ⟹  𝔪_A B ⊆ 𝔪_B²  **
HTGeometry/MvPolynomialLocalizationCotangent.lean          (built)
    mvPolynomialLocalizationCotangentBasis                 (arbitrary base ring)
    mvPolynomialLocalizationCotangentBasis_repr_D_algebraMap
        ** in the localized cotangent basis, D f has the partial derivatives of f **
HTGeometry/KaehlerJacobianRamification.lean                (built)
    not_subsingleton_kaehler_of_not_isUnit_det
    map_maximalIdeal_le_sq_of_not_isUnit_det
        ** ¬ IsUnit (det of the coordinate Jacobian)  ⟹  𝔪_A B ⊆ 𝔪_B²  =  (R) **
HTGeometry/DifferentIdealKaehlerAnnihilator.lean           (built)
    differentIdeal_eq_annihilator_kaehler
        ** the Dedekind different is the Kähler different, for a Dedekind order over a local
           domain with characteristic-zero residue field **
```

`LocalizedMvPolynomialCotangent` (already in the tree, over `ℂ`) supplied the pattern for the
arbitrary-base version; only the base ring had to be generalized.

### What remains for `(R)`, exactly

Only the instantiation, and it is now a list of identifications rather than new mathematics:

```text
k := K,  B := the source Schur DVR       criticalSchurSourceValuationSubring
                                         ≅ Localization.AtPrime (criticalSchurPrimeDivisor)
         A := the observation Schur DVR  criticalSchurObservationValuationSubring
         y := the observation coordinates criticalFieldObservation, as elements of A
         b := mvPolynomialLocalizationCotangentBasis K (criticalSchurRamificationIdeal)
    hgen := D_mem_of_isLocalization ∘ D_mem_of_adjoin_eq_top     (A is K(y) localized)
    hdet := the coordinate Jacobian determinant is the Schur ramification polynomial,
            which lies in the Schur prime                        criticalSourceReciprocal-
                                                                 Jacobian_det_eq_schurRamification
  ⟹ 𝔪_A B ⊆ 𝔪_B²  ⟹  2 ≤ e(Q₀ | 𝔪_A)
  ⟹ 2 ≤ e(W | 𝔪_A) ≤ ramificationIdxIn      (W the normal-closure Schur place above Q₀)
```

### Lean progress — `dY = -Y² dX` as a Kähler identity, and the factorization that removes a basis

```text
HTGeometry/PolynomialDerivationReciprocal.lean             (built)
    polyD                    coefficientwise extension of a derivation to polynomials,
                             valued in PolynomialModule
    polyD_add, polyD_mul, polyD_one, polyD_X_pow           Leibniz and the constants
    coeff_X_pow_smul_of_lt
    polyD_reciprocal
        ** X^L ∣ f g − 1  ⟹  d (g_l) = −∑_{i+j=l} (g²)_i • d (f_j)  for l < L **
HTGeometry/KaehlerJacobianFactorization.lean               (built)
    coordinate_matrix_mul            [v]_b = [w]_b · P  when  v j = ∑ P i j • w i
    not_isUnit_det_of_eq_smul_comb
    map_maximalIdeal_le_sq_of_factorized_jacobian
        ** the auxiliary family w need NOT be a basis **
```

`polyD_reciprocal` is the exact Kähler form of the corpus's `criticalReciprocalInfinitesimal`
identity: in the differentials of the *raw* coordinates, the differential of the reciprocal
coefficient `c_l` has coordinates `−(Y²)_{l−j}`, i.e. the rectangular Schur Toeplitz row.  So the
observation Jacobian in the raw differentials is the block matrix

```text
rows  a_{m+i}  :  the identity on the high raw columns
rows  c_{n+j}  :  −(Y²)_{n+j−k}
```

whose determinant is, by `IdentityCornerDeterminant.associated_det_of_identity_columns`, the
`m × m` determinant `criticalReciprocalJacobian`, already identified with the Schur ramification
polynomial.

`KaehlerJacobianFactorization` is the step that makes this usable: because the coordinate matrix of
a family changes by *right* multiplication, only the transition matrix `P` (the raw Jacobian) needs
a non-unit determinant — the intermediate family `w = {D a_i}` never has to be shown to be a basis.
The basis may therefore be taken from **whatever presentation of the local ring is available**,
which in this tree is the Schur-coordinate one.

### The remaining wiring, in dependency order

```text
(A) a basis of Ω[B⁄K] for B the source Schur DVR
        = present B as a localization of the Schur coordinate polynomial ring
          (criticalSchurSourceValuationRingEquiv + IsDiscreteValuationRing.equivValuationSubring),
          then mvPolynomialLocalizationCotangentBasis
(B) D (observation coordinate) = ∑ (raw Jacobian) • D (raw coordinate)   PolynomialDerivationReciprocal
(C) det (raw Jacobian) ∈ 𝔪_B                                            corpus, twice over
(D) D a ∈ span {D y_j} for a in the observation DVR                     KaehlerRelativeSpan
(E) the instance stack: Algebra K A, Algebra A B, IsScalarTower, IsLocalHom,
    EssFiniteType A B, IsSeparable (ResidueField A) (ResidueField B), 𝔪_A B ≠ ⊥
(F) transport 𝔪_A B ⊆ 𝔪_B² to 2 ≤ ramificationIdxIn 𝔪_A C for the normal closure C
```

Everything general is now proved; `(A)`–`(F)` are identifications inside this tree.

### Lean progress — step `(A)` is CLOSED: the source Schur place has a coordinate cotangent basis

```text
HTGeometry/MvPolynomialLocalizationCotangent.lean          (extended, built)
    localizationCotangentBasis                 for ANY localization, not just Localization.AtPrime
    localizationCotangentBasis_repr_D_algebraMap
HTGeometry/CriticalSchurSourceCotangent.lean               (built)
    criticalSchurCoordinateLocalizationEquiv
        Localization.AtPrime (Schur prime) ≃+* criticalSchurCoordinateValuationSubring
    criticalSchurSourceLocalizationEquiv
        Localization.AtPrime (Schur prime) ≃+* criticalSchurSourceValuationSubring
    criticalSchurSourceValuationAlgebra          Schur coordinate ring acts
    criticalSchurSourceValuation_isLocalization
        ** the actual source Schur valuation ring IS a localization of the coordinate ring **
    criticalSchurSourceValuationGroundAlgebra, criticalSchurSourceValuationGroundTower
    criticalSchurSourceCotangentBasis
        ** Ω[B⁄K] is free on the Schur coordinate differentials **
```

The transport was three lines: `IsDiscreteValuationRing.equivValuationSubring` matches
`criticalSchurCoordinateValuationSubring` definitionally, and
`IsLocalization.isLocalization_of_algEquiv` moves the localization property across the composite.

### Lean progress — steps `(B)`, `(C)`, `(E)` are CLOSED, and `(A)` is CLOSED

```text
HTGeometry/CriticalSchurSourceIntegralModels.lean          (built)
    criticalSourceRawIntegral, criticalSourceRecipIntegral
    criticalSourceRawPolynomialIntegral, criticalSourceRecipPolynomialIntegral
    X_pow_dvd_criticalSourceIntegral_mul_sub_one
    D_criticalSourceRecipPolynomialIntegral_coeff            ** (B): dY = −Y² dX at the place **
HTGeometry/CriticalSchurObservationSourceAlgebra.lean       (built)
    coe_algebraMap_criticalSchurSourceValuation
    coe_algebraMap_ground_criticalSchurSourceValuation
    criticalSchurObservationGroundAlgebra
    criticalSchurObservationSourceAlgebra, …_isLocalHom
    criticalSchurObservationSourceTower
    criticalSchurSourceValuation_essFiniteType_ground / _observation
    criticalSchurResidue_isAlgebraic                         ** κ_B/κ_A is algebraic **
    criticalSchurObservation_map_maximalIdeal_ne_bot         ** (E) **
HTGeometry/ValuationSubringResidueAlgebraic.lean            (built)
    exists_max_valuation
    valuationSubringComapAlgebra, …_isLocalHom
    isAlgebraic_residueField_comap
        ** the residue extension of a pulled-back valuation subring along an algebraic field
           extension is algebraic — hence separable in characteristic zero **
```

With `criticalSchurResidue_isAlgebraic` the residue separability instance that
`Algebra.FormallyUnramified.of_map_maximalIdeal` demands is now automatic
(`Algebra.IsSeparable.of_integral`, the residue field having characteristic zero by
`criticalObservationSchurResidue_charZero`).  Step `(C)` — the coordinate Jacobian determinant is
the Schur uniformizer, hence not a unit — is `det_criticalReciprocalJacobianIntegral` together with
`irreducible_criticalSchurJacobianDetElement`.

## The exact geometric input `(R)` still needs, isolated

`(D)` of the route — the hypothesis `hgen` of `map_maximalIdeal_le_sq_of_factorized_jacobian`, i.e.

```text
∀ a in the observation Schur DVR A,  D a ∈ span_B { D y_j }
```

is **not** bookkeeping, and it is worth recording exactly why, because two different-looking
attacks both land on the same wall.

`hgen` holds if and only if `A` is the localization of the observation coordinate ring `K[y]` at
`q := 𝔪_A ∩ K[y]`, equivalently if and only if `q` has **height one**.  A valuation ring of `K(y)`
whose centre `q` has height ≥ 2 (a blow-up valuation) satisfies every other hypothesis already
proved — including `κ_B/κ_A` algebraic — so no amount of further valuation theory closes it.  The
explicit witness: for `φ(x₁,x₂) = (x₁x₂, x₂)` the ring `A = B ∩ F` is the valuation ring of
`{x₂ = 0}`, its centre on `K[y]` is the maximal ideal `(y₁,y₂)`, `Ω[B⁄A] = 0`, and the Jacobian
determinant is nevertheless a non-unit.  What excludes this in the horizon situation is that the
critical map is **finite** on the chart: a finite morphism does not contract a divisor, so the
image of the Schur divisor is again a divisor and `q` has height one.

**The cheapest Lean form of that input.**  Height one for `q` follows from

```text
Algebra.IsAlgebraic κ_O κ_B ,   κ_O := Frac (K[y] ⧸ q)
```

and, since `κ_B` is generated over `K` by the residues of the raw source coordinates and the
observation coordinates already contain `a_m, …, a_{L−1}`, this reduces to

```text
for i < m,  a_i is INTEGRAL over the observation coordinate ring with the marked
            coordinates inverted, K[y][ (a_m c_n)^{-1} ]
```

— a monic relation reduces modulo the Schur place to a monic relation, which is exactly the
statement that fails for a contraction.  The marked coordinates are units at the Schur place
(`CriticalSchurMarkedUnits.isUnit_criticalSourceRaw_marked_sourceValuationSubring`), so the
reduction is legitimate.

This is §1's "the critical map is finite after restricting to the stated open base" in the precise
ring-theoretic form the ramification argument consumes, and it is the only geometric input left in
`(R)`.

### The remaining `(R)` chain, fully decided

The finiteness input has an exact Lean route, and the tree already owns its hardest ingredient.

```text
(i)   valuative integrality of the low coordinates
        for every valuation subring V of the source field containing the observation
        coordinates and the inverses of the two marked ones, every raw coordinate is in V
      PROOF: if not, scale the low blocks by the inverse of a coordinate of minimal value,
             reduce modulo 𝔪_V, and apply
             critical_biprojective_boundary_exclusion_of_marked_coefficients   (already in the tree)
             — the reduced homogenizing coordinate is 0 while the reduced low block is not,
             which that theorem forbids.  The marked coefficients survive reduction precisely
             because they were inverted.
      ⟹ S := Ro'[a_0 … a_{m-1}, c_0 … c_{n-1}] is finite over Ro' := K[y][(a_m c_n)^{-1}]
(ii)  S is a localization of the Schur coordinate ring, so P'' := 𝔪_B ∩ S has height one
(iii) going-down for the integral extension Ro' ⊆ S with Ro' normal gives height q' = 1,
      q' := 𝔪_A ∩ Ro'
(iv)  hence (Ro')_{q'} is a DVR dominated by A inside the same fraction field, so A = (Ro')_{q'},
      which is exactly `hgen` through D_mem_of_isLocalization + D_mem_of_adjoin_eq_top
(v)   map_maximalIdeal_le_sq_of_factorized_jacobian  ⟹  𝔪_A B ⊆ 𝔪_B²
(vi)  transport to 2 ≤ ramificationIdxIn 𝔪_A C for the normal closure C
```

Step `(i)` is the mathematical content — it is §1's finiteness — and the boundary exclusion it needs
is already an unconditional theorem here.  Everything after it is standard commutative algebra.

### Lean progress — step `(C)` is CLOSED

```text
HTGeometry/CriticalSchurIntegralJacobian.lean              (built)
    map_criticalReciprocalJacobianIntegral
    det_criticalReciprocalJacobianIntegral
        ** det of the integral reciprocal Jacobian = criticalSchurJacobianDetElement,
           which is irreducible, hence not a unit **
```

### Lean progress — step `(i)` is CLOSED: §1's finiteness is now a ring-theoretic theorem

```text
HTGeometry/CriticalLowBlockValuativeIntegrality.lean       (built)
    exists_scaling            in a valuation ring one of finitely many elements divides the rest,
                              normalized so that the scaling is trivial or one product is 1
    valLift, valLift_map, valLift_coeff, valLift_natDegree_le
    coeffs_mem_of_criticalRelation
        ** tails in O with marked coefficients units  ⟹  both low blocks have coefficients in O **
HTGeometry/CriticalSourceLowValuativeIntegrality.lean      (built)
    algebraMap_criticalObservationRaw / _Recip
    coeff_map_criticalObservationRawTail_mem / _Recip…_mem
    coeff_map_criticalObservationRawTail_marked / _Recip…_marked
    criticalSourceLow_mem_valuationSubring
        ** every valuation subring of the source field containing the observation coordinates and
           inverting the two marked ones contains every low raw and low reciprocal coordinate **
HTGeometry/CriticalSourceChartIntegrality.lean             (built)
    criticalObservationRaw_ne_zero, criticalObservationRecip_ne_zero
    criticalSourceRaw_marked_ne_zero, criticalSourceRecip_marked_ne_zero
    criticalObservationChart
    criticalSourceLow_isIntegral_chart
        ** the low raw and low reciprocal coordinates are INTEGRAL over the subring generated by
           the observation coordinates and the inverses of the two marked ones **
```

The valuative criterion is mathlib's `iInf_valuationSubring_superset` (the integral closure of a
subset of a field is the intersection of the valuation subrings containing it); the geometric input
is the tree's own `critical_biprojective_boundary_exclusion_of_marked_coefficients`.

**Overlap noted, so no session rebuilds either.**  `ValuationCriticalFibreIntegrality.
valuationSubring_criticalFibre_coefficients_mem_of_marked_reduction` is a sibling of
`coeffs_mem_of_criticalRelation`: it is phrased for a `criticalFibre` point with tails already over
the valuation subring and needs the reduced tails to be divisible by the corresponding powers of
`X`; the new one is phrased for fraction-field data and needs only invertibility of the marked
coefficients.  Either can drive the argument; the new one wired more directly into the horizon
splitting.

`(R)` now needs only the commutative algebra `(ii)`–`(vi)`: height one for the centre, the DVR
identification of the observation Schur place, `hgen`, and the transport to `ramificationIdxIn`.

### Lean progress — the Schur coordinates are polynomial in the horizon coordinates

```text
HTGeometry/CriticalSchurCoordinateAdjoin.lean              (built)
    criticalSourceCoordinateSet
    criticalSourceScale_mem_adjoin
    criticalSourceReciprocalPolynomial_coeff_mem_adjoin
    criticalSourceReciprocalSquarePositive_mem_adjoin
    criticalSourceSchurCoordinates_mem_adjoin
        ** every Schur coordinate lies in the algebra generated by the raw and reciprocal
           coordinates **
```

This is what makes the Schur local ring `B` a localization of the finite chart algebra
`T := adjoin (chart ring) {raw, reciprocal coordinates}`, and hence what gives `height P'' = 1` for
`P'' := 𝔪_B ∩ T` without circularity: `Rs ⊆ T ⊆ B` and `B` is the localization of `Rs`, so
`B = T_{P''}`, a DVR.

### `(R)`'s remaining chain, corrected once more

An earlier plan tried to reach `height q' = 1` through a dimension formula
(`height p + dim (R/p) = dim R` for finitely generated domains).  **mathlib does not carry that
formula**, and building it needs Noether normalization plus catenarity.  It is not needed:
mathlib's `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` together with the going-down
instance for an integral extension of a normal domain
(`Mathlib/RingTheory/IntegralClosure/GoingDown.lean`) gives

```text
height P'' = height q' + height (fibre)        ⟹   height q' ≤ height P'' = 1
```

and `q' ≠ 0` closes it.  Recorded so no session reaches for the dimension formula again.

Remaining, in order:

```text
1. Rloc := the observation coordinate polynomial ring localized away from the marked product,
   with its injective map to the source field         (normal, Noetherian)
2. T := adjoin Rloc {raw, reciprocal coordinates}      integral and module-finite over Rloc
3. Rs ⊆ T                                              CriticalSchurCoordinateAdjoin  DONE
4. IsLocalization P''.primeCompl B                     ⟹ height P'' = 1
5. going-down                                          ⟹ height q' = 1
6. (Rloc)_{q'} is a DVR dominated by A                 ⟹ A = (Rloc)_{q'}
7. hgen, then map_maximalIdeal_le_sq_of_factorized_jacobian
8. transport to 2 ≤ ramificationIdxIn for the normal closure
```

### Lean progress — steps 1 and 2 of the `(R)` tail are CLOSED

```text
HTGeometry/CriticalSourceSubringIntegrality.lean           (built)
    isIntegral_of_isIntegral_range        integrality over the image subring descends to the ring
    criticalSourceLow_isIntegral_subring  ** integral over ANY subring containing the chart **
HTGeometry/CriticalObservationCoordinateRing.lean          (built)
    criticalObservationRing, criticalObservationRingToField, …Algebra, …Tower
    criticalObservationFracEquiv
    criticalObservationRing_isFractionRing
        ** the observation field is the fraction field of the observation coordinate ring **
    coe_aeval_criticalObservationCoord, criticalObservationRingToField_apply
    criticalObservationRingSourceAlgebra, …Tower
    algebraMap_criticalObservationRing_X_inl / _inr
    criticalObservationMarked, algebraMap_criticalObservationMarked
HTGeometry/CriticalObservationChartRing.lean               (built)
    isUnit_algebraMap_criticalObservationMarked
    criticalObservationChartRing := Localization.Away (marked)
    criticalObservationChartRingAlgebra, …Tower
    criticalObservationMarked_ne_zero
    criticalObservationChartRing_isIntegrallyClosed        (localization of a polynomial ring)
    algebraMap_chartRing_invSelf, criticalObservationChart_subset_range
    criticalSourceCoordinate_isIntegral_chartRing
        ** every horizon coordinate is integral over the chart ring **
    criticalSourceChartAlgebra, criticalSourceChartAlgebra_isIntegral
        ** the chart algebra is an integral extension of an integrally closed ring:
           exactly the input of mathlib's going-down instance **
```

Positivity is carried as `Fact (0 < m)`, `Fact (0 < n)` so that the algebra structures can be
instances; call sites supply `haveI : Fact _ := ⟨hm⟩`.

Remaining on the `(R)` tail: `Rs ⊆ T` at the chart-ring level (the ground-field version is
`criticalSourceSchurCoordinates_mem_adjoin`), `IsLocalization P''.primeCompl B`, going-down for
`height q' = 1`, the DVR identification `A = (chart ring)_{q'}`, `hgen`, and the transport to
`ramificationIdxIn`.

### Lean progress — the chart tower `Rs ⊆ T ⊆ B` is CLOSED

```text
HTGeometry/CriticalSchurChartInclusion.lean                (built)
    criticalSourceCoordinateSet_subset_schur
    criticalObservationRingGroundTower
    observationRing_mem_schur                the observation coordinate ring is integral there
    isUnit_algebraMap_marked_schur           the marked product is a unit there
    chartRing_mem_schur                      ** the whole chart ring is integral there **
    criticalSchurSourceSubalgebra
    criticalSourceChartAlgebra_le_schur      ** T ⊆ B **
HTGeometry/CriticalSchurChartAlgebra.lean                  (built)
    algebraMap_ground_mem_chartAlgebra, adjoinGround_le_chartAlgebra
    schurCoordinateAeval_mem_chartAlgebra    ** Rs ⊆ T **
    chartAlgebraToSchur, chartAlgebraSchurAlgebra, chartAlgebraToSchur_injective
```

So `Rs ⊆ T ⊆ B` with `B` the localization of `Rs` at the Schur prime: the next step,
`IsLocalization P''.primeCompl B` over `T`, is now purely formal, and it yields `height P'' = 1`
because `B` is a DVR.

**A name collision was caught and fixed.**  `criticalSourceRaw_marked_ne_zero` and
`criticalSourceRecip_marked_ne_zero` already exist in `CriticalSchurMarkedUnits` (with `1 < m`,
`1 < n`); the versions proved here for `0 < m`, `0 < n` are now
`criticalSourceRaw_atMarkedIndex_ne_zero` / `criticalSourceRecip_atMarkedIndex_ne_zero`.  The
umbrella does not elaborate if two modules declare the same name — check the whole tree, not just
the file, before naming.

### Lean progress — the Schur place is a height-one point of the chart algebra

```text
HTGeometry/CriticalSchurChartHeight.lean                   (built)
    schurRingToChartAlgebra, chartAlgebraToSchur_schurRingToChartAlgebra
    criticalSchurChartPrime, …_isPrime
    criticalSchurChartPrime_isLocalization
        ** B is the localization of the chart algebra at the centre of the Schur place **
    criticalSchurChartPrime_height       ** that centre has height one **
HTGeometry/CriticalChartTowerFinite.lean                   (built)
    algebraMap_observationRing_injective, algebraMap_chartRing_injective
    chartAlgebra_faithfulSMul
    criticalSourceCoordinateSet_finite
    chartAlgebra_module_finite           the chart algebra is a finite chart-ring module
    chartRing_isNoetherianRing, chartAlgebra_isNoetherianRing
    chartRingObservationFieldAlgebra, …Tower, chartRing_isFractionRing
        ** the observation field is the fraction field of the chart ring **
```

All hypotheses of mathlib's going-down instance
(`[IsDomain S] [FaithfulSMul R S] [Algebra.IsIntegral R S] [IsIntegrallyClosed R]`) and of
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` are now in place for the pair
(chart ring, chart algebra).  Next: `height q' = 1` for the centre `q'` on the chart ring — the
alternative `q' = ⊥` is excluded by `criticalSchurObservationValuationSubring_ne_top`, since it
would put the whole observation field inside the Schur valuation ring.

### Lean progress — step 6 is CLOSED: the centre on the chart ring has height one

```text
HTGeometry/CriticalChartCentreHeight.lean                  (built)
    chartRing_isDomain
    chartRingSourceTower                     the two chart-ring maps into the source field agree
    criticalSchurChartUnder, …_isPrime, …_liesOver
    criticalSchurChartUnder_ne_bot
        ** the centre is nonzero, because otherwise the whole observation field would be
           integral at the Schur place **
    criticalSchurChartUnder_height           ** height q' = 1 **
```

The height transfer is mathlib's `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` with the
going-down instance for an integral extension of an integrally closed domain; the only extra input
is that the centre is not the zero ideal, which the corpus's
`criticalSchurObservationValuationSubring_ne_top` supplies.

What remains of `(R)`:

```text
7. (chart ring)_{q'} is a DVR (height one in a normal Noetherian domain) and equals A,
   because a discrete valuation ring is a maximal proper subring of its fraction field
8. hgen, then map_maximalIdeal_le_sq_of_factorized_jacobian
9. transport 𝔪_A B ⊆ 𝔪_B² to 2 ≤ ramificationIdxIn for the normal closure
```

### Lean progress — step 7 is CLOSED: `A` is the chart local ring

```text
HTGeometry/CriticalChartLocalRing.lean                     (built)
    criticalChartLocalRing := Localization.AtPrime (centre)
    criticalChartLocalRing_isDVR            height one in a normal Noetherian domain
    criticalChartLocalRingAlgebra, …Tower, …_isFractionRing
    mem_criticalSchurChartUnder_iff
    algebraMap_chartRing_observationField_mem_schur
    isUnit_chartRing_schur_of_notMem, isUnit_chartRing_observation_of_notMem
HTGeometry/CriticalSchurObservationChartLocal.lean          (built)
    notUnit_chartRing_observation_of_mem
    criticalSchurObservation_isInteger_chartLocal
        ** every element of the observation Schur valuation ring is r / s with r, s in the chart
           ring and s outside the centre **
```

The argument is the standard one for valuation rings: `ValuationRing.isInteger_or_isInteger` splits
an element of the fraction field, and in the inverse branch the numerator would have to be a
non-unit of the chart local ring, which contradicts the element being a unit of the observation
Schur place.

`(R)` now needs only

```text
8. hgen — immediate from step 7 through D_mem_of_isLocalization + D_mem_of_adjoin_eq_top —
   and then map_maximalIdeal_le_sq_of_factorized_jacobian
9. transport 𝔪_A B ⊆ 𝔪_B² to 2 ≤ ramificationIdxIn for the normal closure
```

### Lean progress — `A` as an `IsLocalization`, and the algebra towers to the Schur places

```text
HTGeometry/CriticalSchurObservationLocalization.lean       (built)
    chartRingToObservationSchur, chartRingObservationSchurAlgebra
    criticalSchurObservation_isLocalization
        ** IsLocalization (centre).primeCompl (observation Schur valuation ring) **
    chartRingSchurSourceAlgebra, chartRingSchurSourceTower
    observationRingSchurSourceAlgebra, observationRingChartSchurTower
    coe_algebraMap_observationRing_schur
    observationRingSchurGroundTower, chartRingSchurGroundTower, observationSchurGroundTower
```

The instance `criticalSchurObservation_isLocalization` is the exact hypothesis of
`KaehlerRelativeSpan.D_mem_of_isLocalization`, and the ground towers let it be applied with the
ground field as base.  `hgen` is now one application of that lemma followed by one of
`D_mem_of_adjoin_eq_top` over `MvPolynomial.adjoin_range_X`.

### Lean progress — `hgen` is CLOSED

```text
HTGeometry/CriticalSchurGenerationHypothesis.lean          (built)
    observationRingObservationSchurAlgebra and the four remaining algebra towers
    criticalObservationCoordSchur
    criticalSchur_hgen
        ** D (anything from the observation Schur place) lies in the span of the differentials of
           the observation coordinates **
```

The proof is three applications of `KaehlerRelativeSpan`: localize the observation Schur place down
to the chart ring (`criticalSchurObservation_isLocalization`), localize the chart ring down to the
observation coordinate ring (`Localization.Away` of the marked product), and then use
`MvPolynomial.adjoin_range_X`.

`hgen` was the crux of `(R)` — the hypothesis that is false for a map that contracts the Schur
divisor — and it is now unconditional.  What is left of `(R)` is arithmetic bookkeeping:

```text
hvw   D (observation coordinate) = ∑ (raw Jacobian) • D (raw coordinate)
      — the reciprocal rows are D_criticalSourceRecipPolynomialIntegral_coeff, the raw rows are
        the identity, and the block determinant is IdentityCornerDeterminant
hdet  ¬ IsUnit (det (raw Jacobian))
      — det_criticalReciprocalJacobianIntegral together with
        irreducible_criticalSchurJacobianDetElement
then  map_maximalIdeal_le_sq_of_factorized_jacobian   gives   𝔪_A B ⊆ 𝔪_B²
then  transport to 2 ≤ ramificationIdxIn for the normal closure
```

### Lean progress — the observation Jacobian, set up in block order

```text
HTGeometry/CriticalObservationJacobianBlocks.lean          (built)
    coe_algebraMap_criticalObservationCoordSchur
    algebraMap_criticalObservationCoordSchur_inl / _inr
        ** the observation coordinates, seen in the source Schur ring, ARE the marked raw and
           reciprocal integral coordinates **
    criticalRawDifferential      the auxiliary family w, indexed by Fin m ⊕ Fin n through
                                 finSumFinEquiv (low raw block first, then high)
    criticalObservationBlockCoord   the family y in the matching block order
    criticalObservationJacobian     the matrix P: identity on the raw block, rectangular Schur
                                    Toeplitz on the reciprocal block
    criticalObservationJacobian_hvw_inr    ** the identity column of hvw **
```

The block order is chosen so that `P = Matrix.fromBlocks D 0 C 1` and hence
`det P = det D` by `Matrix.det_fromBlocks_zero₁₂`, with `D` the transpose of
`criticalReciprocalJacobian` — whose determinant is the Schur uniformizer, hence not a unit.

Remaining: the reciprocal column of `hvw` (converting the antidiagonal convolution of
`polyD_reciprocal` into the `Fin m ⊕ Fin n` sum), the determinant identification, the application of
`map_maximalIdeal_le_sq_of_factorized_jacobian`, and the transport to `ramificationIdxIn`.

## `(R)` IS PROVED IN LOCAL FORM

```text
HTGeometry/CriticalObservationJacobianRecip.lean           (built)
    criticalRawDifferential_eq, criticalObservationJacobian_apply_inl
    criticalObservationJacobian_hvw_inl        ** the reciprocal column of hvw **
HTGeometry/CriticalObservationJacobianDet.lean             (built)
    criticalObservationJacobian_eq_fromBlocks
    det_criticalObservationJacobian
    not_isUnit_det_criticalObservationJacobian
HTGeometry/CriticalSchurRamifies.lean                      (built)
    criticalBlockIndexEquiv, criticalSchurBlockCotangentBasis
    criticalSchur_hgen_block
    criticalSchur_map_maximalIdeal_le_sq
        ** 𝔪(observation Schur place) · B  ⊆  𝔪(source Schur place)²  **
```

That is obligation `(R)`: the ramification index of the source Schur place over the observation
Schur place is at least two.  Unconditional, no hypotheses beyond `1 < m`, `1 < n` (carried as
`Fact` instances) and the standing `[Field K] [CharZero K] [IsAlgClosed K]`.

The chain, for the record:

```text
critical_biprojective_boundary_exclusion_of_marked_coefficients   (already in the tree)
  → coeffs_mem_of_criticalRelation                                valuative integrality
  → criticalSourceLow_isIntegral_chart                            §1 finiteness, ring form
  → chart algebra integral over the chart ring                    going-down input
  → height (centre on the chart ring) = 1                         going down
  → A = (chart ring) localized at that centre                     valuation-ring maximality
  → hgen                                                          KaehlerRelativeSpan
  → Ω[B⁄A] ≠ 0                                                    non-unit Jacobian determinant
  → 𝔪_A B ⊆ 𝔪_B²                                                 FormallyUnramified.of_map_maximalIdeal
```

What remains for the card: transport this to `2 ≤ ramificationIdxIn 𝔪_A C` for the normal-closure
integral closure `C` (multiplicativity of the ramification index in the tower, or
`Ideal.ramificationIdx'_ne_one_iff` at the source place and `ramificationIdx'_le_ramificationIdx'`),
and then `(D)` and `(P)`.

## OBLIGATION `(R)` IS CLOSED

```text
HTGeometry/CriticalSchurNormalRamifies.lean                (built)
    criticalSchurSourceToNormalUpper, ..._comp
    criticalSchur_normalUpper_map_maximalIdeal_le_sq
    criticalNormalUpper_not_maximalIdeal_le_sq             Nakayama in a DVR
    criticalSchur_normalUpper_map_maximalIdeal_ne
    criticalSchurNormalLocalizationUpperEquiv, ..._comp, ..._map_maximalIdeal
    criticalSchur_map_maximalIdeal_localization_ne
HTGeometry/CriticalSchurRamificationIndex.lean             (built)
    criticalSchur_two_le_ramificationIdx'
    criticalSchur_two_le_ramificationIdxIn
        ** 2 ≤ ramificationIdxIn 𝔪(observation Schur place) (normal integral closure) **
    criticalSchurInertiaGroup_nontrivial                   (instance)
    exists_criticalGeometricMonodromy_isSwap_of_degree
    criticalGeometricMonodromy_eq_top_of_degree_of_isPreprimitive
    criticalGeometricMonodromy_eq_top_of_collision_of_isPreprimitive
```

The transport, for the record.  The local statement `𝔪_A B ⊆ 𝔪_B²` travels along the local
embedding `B → V` of the source Schur valuation ring into the chosen normal-closure Schur valuation
ring, giving `𝔪_A V ⊆ 𝔪_V²`.  Nakayama in the discrete valuation ring `V` (its maximal ideal is
finitely generated and nonzero) gives `𝔪_V² ≠ 𝔪_V`, hence `𝔪_A V ≠ 𝔪_V`.  Since `V` is the
localization of the normal integral closure `S` at the Schur prime `P`
(`criticalSchurNormalLocalizationEquivUpper`), this is exactly the failure of
`Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff`, so `e(P) ≠ 1`; and `e(P) ≠ 0` because `P` lies
over a nonzero prime.  Thus `2 ≤ e(P) = ramificationIdxIn`, the Galois-invariance of the index
(`Ideal.ramificationIdxIn_eq_ramificationIdx`) supplying the last step.

**Card status.**  `(R)` done.  `(D)` (`collisionSupport ≤ 2`, i.e. at most two sheets collide) and
`(P)` (primitivity) remain; both now feed directly into
`criticalGeometricMonodromy_eq_top_of_collision_of_isPreprimitive`, which needs nothing else.

## Lean progress — the Kähler different at the Schur place is the MAXIMAL IDEAL

Two modules, built and wired.

```text
HTGeometry/KaehlerAnnihilatorDeterminant.lean            (built)
    bijective_linearCombination_of_spanning
    basisOfSpanningOfBasis, coe_basisOfSpanningOfBasis
        a spanning family of the size of a basis IS a basis (Orzech)
    det_mem_annihilator_kaehler                Cramer: det P annihilates Ω[B⁄A]
    annihilator_kaehler_eq_maximalIdeal
        ** det P irreducible in the DVR B  ⟹  Ann (Ω[B⁄A]) = 𝔪_B **

HTGeometry/CriticalRawCotangentBasis.lean                (built)
    localizationCotangentBasis_apply           the basis IS the family of variable differentials
    criticalSchurSourceCotangentBasis_apply
    criticalRawSpan, D_criticalSourceRawIntegral_mem, D_criticalSourceRecipIntegral_mem
    criticalSchurSourceInclusion, criticalRawVanishing
    criticalRawSpan_eq_top
        ** the RAW differentials span Ω[B⁄K] **
    criticalRawBlockCotangentBasis              hence they form a basis
    criticalSchur_annihilator_kaehler_eq_maximalIdeal
        ** Ann (Ω[source Schur place ⁄ observation Schur place]) = 𝔪_B **
```

The spanning statement is the one that needed the corpus: `dY = -Y² dX`
(`D_criticalSourceRecipPolynomialIntegral_coeff`) puts the reciprocal differentials in the raw span,
`criticalSourceSchurCoordinates_mem_adjoin` puts the Schur coordinates in the algebra generated by
raw and reciprocal coordinates, and the elements whose differential lies in a fixed submodule form
a subalgebra (`cotangentVanishingSubalgebra`).  With the raw differentials as the basis, the
coordinate matrix of the observation differentials is the observation Jacobian *itself*, whose
determinant `criticalSchurJacobianDetElement` is a uniformizer
(`irreducible_criticalSchurJacobianDetElement`).

### What this buys, and the remaining chain for `(D)`

`(D)` is `|collisionSupport| ≤ 2`, and the dictionary is

```text
|collisionSupport| = Σ_{Q ramified over the Schur place} e_Q · f_Q
```

so `(D)` needs exactly three things beyond `(R)`:

```text
(D-e)  e_{Q₀} = 2 exactly       ⟸ v_{Q₀}(𝔇) = 1 (now proved, in Kähler form)
                                   + Ideal.pow_sub_one_dvd_differentIdeal (mathlib)
(D-f)  f_{Q₀} = 1               ⟸ §3: at most one singular point in the reduced fibre
(D-1)  one ramified prime       ⟸ irreducibility of the Jacobian divisor (corpus)
```

`(D-e)` is now infrastructure only: mathlib's bound needs `A` Dedekind and `B` the *integral
closure* of `A` in the source field, whereas the corpus works with the source Schur *valuation
ring*, which is that integral closure localized at `Q₀`.  Building
`integralClosure (CriticalSchurNormalBaseRing) (criticalSourceField)` and the localization
identification — the exact analogue of `criticalSchurNormalLocalizationEquivUpper`, which already
exists for the normal closure — transports `Ann = 𝔪_B` to `v_{Q₀}(differentIdeal) = 1`.

`(D-f)` is the mathematics.  The clean route, recorded so it is not re-derived: for a singular point
`p` of the reduced fibre with conormal `λ_p`, corank one gives `im (df_p) = ker λ_p`, and
`𝔪_A B ⊆ 𝔪_B²` — which `(R)` now proves — gives `f^*δ ∈ 𝔪_p²` for `δ` the reduced equation of the
branch divisor, hence `d(f^*δ) = 0`, hence `dδ` annihilates `im (df_p)`, hence `λ_p ∥ dδ`.  Since
`dδ` is defined over the residue field of `A`, the same holds for every singular point, so all the
conormals are proportional; §2 (`conormal_determines_tangent_smul`) then scales the tangents to a
common `(U,V)` and `criticalFibre_eq_of_shared_coprime_tangent` collapses the singular points to
one.  The one genuinely new input in that chain is `dδ ≠ 0`, i.e. that the branch divisor is
generically reduced — equivalently the fold condition `⟨d(det Jac), ker⟩ ≠ 0` at the generic point
of the Jacobian divisor.

## Lean progress — `(D-e)` IS CLOSED: the Schur ramification index is exactly two

Three more modules, built and wired.

```text
HTGeometry/AnnihilatorLocalization.lean                     (built)
    annihilator_le_map_annihilator_of_isLocalizedModule
        ** for a finite module, Ann_B(localized) ≤ (Ann_S M)·B **

HTGeometry/CriticalSchurSourceIntegralClosure.lean          (built)
    criticalSchurObservationSourceFieldAlgebra + towers
    CriticalSchurSourceIntegralClosure          integralClosure (obs Schur DVR) (source field)
    Dedekind / finite / faithful / fraction-ring instances
    criticalSchurSourceIntegralClosure_mem_upper, ...ToUpper
    criticalSchurSourceIntegralClosurePrime, _isPrime, _liesOver, _ne_bot
    CriticalSchurSourceLocalization, ...ToUpper, _isLocalHom, _bijective
    criticalSchurSourceUpper_isLocalization
        ** the source Schur valuation ring IS the localization of that integral closure **

HTGeometry/CriticalSchurSourceRamificationIndex.lean        (built)
    criticalSchurObservationResidueField_charZero
    criticalSchur_maxExt_ne_bot
    criticalSchur_differentIdeal_eq_annihilator     Dedekind different = Kähler different
    criticalSchur_maximalIdeal_le_map_differentIdeal
    criticalSchur_differentIdeal_not_le_sq
    criticalSchur_source_ramificationIdx_le_two
    criticalSchurSourceLocalizationUpperEquiv + comp/map_maximalIdeal
    criticalSchur_source_map_maximalIdeal_localization_ne
    criticalSchur_source_ramificationIdx_eq_two
        ** e(source Schur place / observation Schur place) = 2, UNCONDITIONALLY **
```

The upper bound is mathlib's `pow_sub_one_dvd_differentIdeal` fed by the Kähler computation: the
different of the source integral closure equals the annihilator of `Ω[S⁄A]`
(`differentIdeal_eq_annihilator_kaehler`), whose localization at the Schur prime is the maximal
ideal of the source Schur valuation ring (`criticalSchur_annihilator_kaehler_eq_maximalIdeal`), and
the annihilator of a localized finite module is the extension of the annihilator.  So the different
is not contained in the square of the Schur prime, which caps `e − 1` at one.  The lower bound is
`(R)` transported to the same localization.

**`(D)` after this.**

```text
(D-e)  e_{Q₀} = 2                  ** DONE **
(D-f)  f_{Q₀} = 1                  §3 — the conormal/fold argument (see the chain recorded above)
(D-1)  one ramified prime          irreducibility of the Jacobian divisor
(D-c)  |collisionSupport| = e·f    the fibre-to-prime dictionary
```

## `(D-f)` — the route, fully determined (READ THIS BEFORE TOUCHING §3)

The conormal apparatus §2 needs is already complete in the tree:

```text
ConormalLiftObstruction.conormal_eq_zero_of_lifts       liftable ⟹ the conormal functional vanishes
ConormalTangentDetermination.exists_conormal_ne_zero    a nonzero low pair has a nonzero functional
ConormalTangentDetermination.conormal_determines_tangent_smul
    ** proportional conormal functionals ⟹ proportional tangent pairs **
CriticalFibreSharedTangentRigidity.criticalFibre_eq_of_shared_coprime_tangent
```

so §3 needs exactly one thing: **the conormal functionals at two singular points of the reduced
fibre are proportional.**  The following identification settles it, and is the reason no
deformation theory is needed.

**The conormal IS `dδ`, and `dδ` is defined over the base.**  Write `A` for the observation Schur
DVR, `B` for the source Schur valuation ring, `δ` for a uniformizer of `A`, and `P` for
`criticalObservationJacobian`.  Then:

* `Ω[A⁄K]` has the observation coordinates as a cotangent basis — `A` is a localization of
  `criticalObservationRing` (through `criticalObservationChartRing` and `criticalChartLocalRing`),
  so `localizationCotangentBasis` applies exactly as it did for `B`;
* in that basis and the raw basis of `Ω[B⁄K]`, the matrix of `Ω[A⁄K] ⊗ B → Ω[B⁄K]` **is** `P` —
  that is precisely `criticalObservationJacobian_hvw_inl/inr`;
* `(R)` gives `δ · B ⊆ 𝔪_B²`, hence `D(algebraMap A B δ) ∈ 𝔪_B · Ω[B⁄K]`, i.e. the coordinate
  vector `c` of `dδ` satisfies `P c ≡ 0 (mod 𝔪_B)`;
* `c mod 𝔪_B ≠ 0` because `dδ ∉ 𝔪_A Ω[A⁄K]` (the residue field of `A` has transcendence degree
  `L−1`, so the image of `𝔪_A/𝔪_A²` in `Ω[A⁄K] ⊗ k(A)` is a line);
* `ker (P mod 𝔪_B)` is one-dimensional (corank one), so `c mod 𝔪_B` **spans** it.

Since `Ω[A⁄K] ⊗ B → Ω[B⁄K]` is the transpose of the differential of the horizon map, its kernel is
the annihilator of the liftable deformations — the conormal line.  So the conormal line is spanned
by `dδ`, which is defined over `A`; every singular point of the reduced fibre is a residue
embedding `k(Q₀) → k_W` and they all restrict to the same map on `k(A)`, so all the conormal lines
coincide.  `conormal_determines_tangent_smul` then scales the tangents to one `(U,V)` and
`criticalFibre_eq_of_shared_coprime_tangent` collapses the singular points to one, i.e.
`f_{Q₀} = 1`.

**Build order for `(D-f)`.**

```text
1  Ω[A⁄K] coordinate basis            mirror of CriticalRawCotangentBasis for the observation side
2  A as a localization of criticalObservationRing        composite of two localizations
3  dδ ∉ 𝔪_A Ω[A⁄K]                    trdeg of the residue field = L−1
4  D(algebraMap A B δ) ∈ 𝔪_B Ω[B⁄K]   directly from (R)
5  corank one of P mod 𝔪_B            SquareMatrixCorankOne + the surviving cofactor
6  bridge: ker(P mod 𝔪_B) = the corpus's conormal line     via conormal_eq_zero_of_lifts + (5)
7  assemble §3, then f_{Q₀} = 1
```

Nothing in this list is open mathematics; `(3)` and `(6)` are the only ones needing new proofs of
any length.

## Lean progress — `(D-f)` steps 1, 2 and 4 are CLOSED

```text
HTGeometry/CriticalSchurConormalDirection.lean          (built)
    repr_D_mem_maximalIdeal_of_mem_sq                   general Leibniz form
    criticalSchur_repr_D_observation_mem_maximalIdeal
        ** every raw coordinate of the differential of a non-unit of the observation Schur
           place lies in the maximal ideal of the source Schur place **

HTGeometry/CriticalObservationCotangentBasis.lean       (built)
    formallyEtaleCotangentBasis, ..._repr_D_algebraMap, ..._apply
        the coordinate cotangent basis for any formally étale algebra over a polynomial ring
    criticalObservationRingSchur_formallyEtale          composite of two localizations
    criticalObservationSchurCotangentBasis, ..._apply
    criticalObservationBlockCotangentBasis, ..._apply
    criticalObservationJacobian_repr
        ** in the observation and raw bases, the cotangent map has the observation Jacobian
           as its matrix **
    D_algebraMap_eq_sum_blockCoord
    criticalSchur_jacobian_conormal_mem_maximalIdeal
        ** the coordinate vector of the differential of a non-unit of the observation Schur
           place is killed by the Jacobian modulo 𝔪 of the source Schur place **
```

So the conormal line of the branch at the source Schur place is spanned by a vector whose entries
come from the observation side.  What remains of step 3 is that this vector is **nonzero**
modulo the maximal ideal — equivalently, that the branch divisor is generically smooth.  The
elementary proof being built: the centre of the observation Schur place on the observation
coordinate ring is a prime `𝔭`; take `r ∈ 𝔭` nonzero of minimal total degree; if every
`∂r/∂y_s` were again in `𝔭` then, being of smaller total degree, each would vanish, so `r` would be
constant and `𝔭` the unit ideal.  In characteristic zero a polynomial with all partial derivatives
zero is constant (`coeff_pderiv` plus `CharZero`), and differentiation strictly drops the total
degree; both are general `MvPolynomial` facts that this corpus did not have.

## Lean progress — `(D-f)` step 3 is CLOSED: the branch divisor is generically smooth

```text
HTGeometry/CriticalObservationConormalBase.lean          (built)
    totalDegree_pderiv_lt                       differentiation strictly drops total degree
    totalDegree_eq_zero_of_forall_pderiv_eq_zero
        ** in characteristic zero, all partial derivatives zero ⟹ constant **
    criticalObservationSchurCentre               the centre of the Schur place on the coordinate ring
    criticalObservationSchurCentre_isPrime, ..._ne_top
    exists_ne_zero_mem_criticalObservationSchurCentre
    exists_mem_maximalIdeal_repr_D_notMem_maximalIdeal
        ** some non-unit of the observation Schur place has a differential with a UNIT
           coordinate **
```

The proof is the minimal-degree argument: take a nonzero `r` in the centre of minimal total degree;
if every `∂r/∂y_s` were again in the centre it would have to vanish (smaller degree), so `r` would
be constant and the centre the unit ideal.  Both `MvPolynomial` facts were missing from mathlib and
from this corpus.

**State of `(D-f)`.**

```text
1  Ω[A⁄K] coordinate basis           DONE   CriticalObservationCotangentBasis
2  A formally étale over the coordinate ring   DONE   (composite of two localizations)
3  the conormal vector is nonzero    DONE   CriticalObservationConormalBase
4  the conormal vector is killed by the Jacobian   DONE   CriticalSchurConormalDirection
5  corank one of the reduced Jacobian at the source Schur place        NEXT
6  bridge to the corpus's conormal pairing                            after 5
7  assemble §3, then f_{Q₀} = 1
```

For `(5)` the corpus already owns everything: `SchurCofactorLocus.not_dvd_det_submatrix_rectangularSchur`
(the corner cofactor is not divisible by the Schur section, hence does not vanish on the divisor),
`CriticalSchurJacobianDivisor.rectangularSchurToeplitz_actual_eq_invScale_smul_normalized`
(the actual reciprocal Toeplitz matrix is the normalized one up to the inverse scale square), and
`SquareMatrixCorankOne.finrank_ker_mulVecLin_map_eq_one` (`det = 0` plus one surviving minor gives
corank one over any extension field).  What has to be written is the reduction map
`criticalSchurSourceRing → residue field of the source Schur place`, whose kernel is
`criticalSchurPrimeDivisor`, and the observation that the corner cofactor survives it.

### `(D-f)` step 6, worked out in coordinates (so it is not re-derived)

Write `L = m + n`, `A` for the observation Schur DVR, `B` for the source Schur valuation ring,
`P = criticalObservationJacobian`, and `c` for the coordinate vector of the differential of a
non-unit of `A` in the observation cotangent basis.  Steps 3 and 4 give `P c ≡ 0 (mod 𝔪_B)` with
`c ≢ 0`.

**`P` is the transpose of the differential of the horizon map.**  Its `(t, s)` entry is
`∂y_s/∂x_t`, so for a source deformation `δx` the induced observation deformation is
`δy_s = Σ_t P t s · δx_t`.  Hence for every source deformation

```text
Σ_s c_s · δy_s  =  Σ_t δx_t · (Σ_s P t s c_s)  =  0 ,
```

i.e. `c` annihilates every liftable observation deformation — the same property
`ConormalLiftObstruction.conormal_eq_zero_of_lifts` proves for the conormal functional `λ_{U,V}` of
a tangent pair.

**The corpus's "liftable" set is exactly that image.**  A deformation `(δP, δQ)` lifts iff there
are low `(da, db)` with `X^L ∣ (da + δP)Y + A(db + δQ)`.  Multiplying by `Y` and using `AY ≡ 1`
turns this into `X^L ∣ (da + δP)Y² + (db + δQ)`, i.e. `db + δQ = −Y²(da + δP)` — which is precisely
`δ(recip) = −Y² δ(raw)` for the source deformation `δx = da + δP`.  So liftable deformations are
the image of the differential, of dimension `L − 1` by corank one.

**Conclusion.**  `λ_{U,V}` and `c` both annihilate an `(L−1)`-dimensional subspace of an
`L`-dimensional space and both are nonzero, hence are proportional.  Since `c` comes from `A`, its
image is the same under every residue embedding `k(Q₀) → k_W`, so the conormal functionals at all
singular points of the reduced fibre are proportional — which is exactly the hypothesis of
`conormal_determines_tangent_smul`, and then of `criticalFibre_eq_of_shared_coprime_tangent`.

As a vector in the observation cotangent basis, `λ_{U,V}` is `(U reversed, −V reversed)`: the
coefficient of `dq_j` is `U_{L-1-j}` and of `dp_i` is `−V_{L-1-i}`.

## Lean progress — `(D-f)` step 5's infrastructure

```text
HTGeometry/CriticalObservationJacobianMinor.lean          (built)
    finrank_ker_mulVecLin_eq_one_of_det_eq_zero'
        corank one over ANY finite index type (the corpus version was `Fin (N+1)`-only)
    det_criticalObservationJacobian_map_residue           the Jacobian is singular at the place
    det_submatrix_criticalObservationJacobian
        ** deleting one raw row and column from the observation Jacobian leaves exactly the
           corresponding minor of the reciprocal Jacobian **

HTGeometry/CriticalSchurResidueReduction.lean             (built)
    mvPolynomialDropFirst, mvPolynomialDropFirst_rename_succ
    mem_span_of_rename_succ_mem_span
        ** the variable shift reflects membership in a principal ideal **
    map_aeval_rectangularSchurToeplitz
        the universal Schur matrix evaluates to the normalized reciprocal-square Toeplitz matrix
    criticalSchur_residue_algebraMap_eq_zero_iff
        a Schur coordinate polynomial has zero residue exactly on the ramification ideal
```

What is left of step 5 is the index bridge: `SchurCofactorLocus` states the corner-cofactor facts
for `rectangularSchurToeplitz (schurVar K (n'+m'-1+2)) (n'+1) (m'+1)` while the actual objects use
`rectangularSchurToeplitz (schurVar K (m+n-1)) n m`.  With `m = m'+1`, `n = n'+1` and `m' ≥ 1`
these agree, but the identification needs the `finCongr` rename that
`rename_finCongr_det_rectangularSchurToeplitz` already performs for the determinant; the same has
to be done for the corner minor.  After that, `not_dvd_det_submatrix_rectangularSchur` plus
`mem_span_of_rename_succ_mem_span` plus `criticalSchur_residue_algebraMap_eq_zero_iff` give the
surviving minor, and `finrank_ker_mulVecLin_eq_one_of_det_eq_zero'` gives corank one at the
residue field of the source Schur place.

## Lean progress — `(D-f)` step 5 is CLOSED: corank one at the source Schur place

```text
HTGeometry/CriticalSchurCornerCofactor.lean               (built)
    rename_finCongr_det_submatrix_rectangularSchurToeplitz
    not_dvd_det_submatrix_rectangularSchur_actual
    criticalSchur_cornerCofactor_notMem_ramificationIdeal
        ** the corner cofactor of the actual Schur section is not in the ramification ideal **

HTGeometry/CriticalSchurJacobianCorankOne.lean            (built)
    criticalSourceSchurCoordinates_comp_succ
    aeval_criticalSourceSchurCoordinates_rename_succ
    coe_det_submatrix_criticalReciprocalJacobianIntegral
        every minor of the integral reciprocal Jacobian, in closed form
    residue_det_submatrix_criticalReciprocalJacobianIntegral_ne_zero
    criticalSchur_finrank_ker_reduced_jacobian_eq_one
        ** the kernel of the reduced observation Jacobian is a LINE **
```

The reciprocal Jacobian is the negative normalized Schur Toeplitz matrix scaled by the inverse
square of the source scale, so each of its minors is a unit multiple of the corresponding minor of
the universal Schur section evaluated at the Schur coordinates.  The determinant vanishes at the
Schur place while the corner cofactor does not, and the corank-one criterion (now stated for an
arbitrary finite index type) gives a one-dimensional kernel.

**State of `(D-f)`.**

```text
1  Ω[A⁄K] coordinate basis                        DONE
2  A formally étale over the coordinate ring      DONE
3  the conormal vector is nonzero                 DONE
4  the conormal vector is killed by the Jacobian  DONE
5  corank one of the reduced Jacobian             DONE
6  bridge to the corpus's conormal pairing        NEXT (worked out in coordinates above)
7  assemble §3, then f_{Q₀} = 1
```

## Lean progress — `(D-f)` step 6 is CLOSED

```text
HTGeometry/HorizonConormalJacobianKernel.lean             (built)
    sum_fin_toeplitz_eq_coeff_mul        a truncated Toeplitz row is a coefficient of a product
    sum_toeplitz_rev_eq_neg_coeff        the same, against reversed coefficients
    horizonConormalVector                (U reversed, −V reversed) in block order
    horizonObservationJacobian           the observation Jacobian for a general reciprocal jet
    horizonObservationJacobian_mulVec_conormal
        ** the conormal vector of a low tangent is a KERNEL VECTOR of the observation Jacobian **

HTGeometry/HorizonConormalProportional.lean               (built)
    exists_smul_of_finrank_ker_eq_one    a nonzero vector spans a one-dimensional kernel
    tangent_smul_of_conormal_smul
        ** proportional conormal vectors ⟹ proportional tangent pairs **
```

The first proof is the identity `V ≡ −Y²U` below the horizon: on the reciprocal block the Toeplitz
row computes `−(Y²U)` at an index at least `n`, where `V` vanishes; on the raw block it computes
`−(Y²U) = V` at the matching index, cancelling the diagonal entry of the identity corner.  No
deformation theory and no reference to the corpus's conormal *pairing* is needed — the conormal
vector is characterised purely as a kernel vector.

**State of `(D-f)`.**  Steps 1–6 are closed.  What remains is step 7, the corpus-level assembly:

```text
(a)  the two singular points of the reduced fibre are two residue embeddings k(Q₀) → k_W, and the
     Jacobian at each is the image of the ONE matrix P mod 𝔪_B under that embedding;
(b)  the conormal vector c of step 3/4 lies in ker (P mod 𝔪_B), is nonzero, and is fixed by both
     embeddings because it comes from k(A);
(c)  hence by exists_smul_of_finrank_ker_eq_one and tangent_smul_of_conormal_smul the two tangent
     pairs are proportional; scale them to a common (U,V);
(d)  criticalFibre_eq_of_shared_coprime_tangent then identifies the two points, so f_{Q₀} = 1.
```

`(a)` is the only remaining piece needing new corpus wiring: the dictionary between points of the
reduced fibre and residue embeddings of the source Schur place.  That same dictionary is what
`(D-c)` needs, so it should be built once.

## Lean progress — collisions are singular points of the reduced fibre

```text
HTGeometry/CriticalSchurCollisionSingular.lean            (built)
    C_uniformizer_dvd_of_map_residue_eq_zero
    criticalSchur_exists_reduced_tangent_of_collision
        ** two colliding sheets produce a NONZERO low tangent at their common reduced state **
```

Two distinct sheets have distinct integral fibre points (`criticalGeometricSheetToSchurFibre_injective`)
whose difference reduces to zero, hence is divisible by a uniformizer, so
`exists_reduced_tangent_of_congruent` applies.  This is the bridge from `collisionSupport` to the
singular locus of the reduced fibre: **every sheet involved in a collision reduces to a point where
the critical Jacobian degenerates.**

Combined with `(D-f)` — at most one such point — this will give
`collisionSupport ⊆ r⁻¹(that one point)`, and the remaining count is the size of that fibre.

## Lean progress — `(D-1)` step 1: the Schur coordinate ring is integral over the Schur place

```text
HTGeometry/CriticalSchurCoordinateIntegral.lean           (built)
    criticalChartSourceGroundTower, criticalChartSchurObservationFieldTower,
    criticalChartSchurSourceTower, criticalSchurObservationGroundFieldTower,
    criticalSchurObservationGroundSourceTower          five scalar towers
    criticalSourceAdjoin_isIntegral_chartRing
    criticalSourceSchurCoordinates_isIntegral
    criticalSchurSourceRing_isIntegral
        ** the whole Schur coordinate ring lands in the integral closure of the observation
           Schur place in the source field **
```

### The route to `(D-1)`, recorded

Write `R_s` for the Schur coordinate ring, `S` for its ramification polynomial, `A` for the
observation Schur DVR, `B'` for the integral closure of `A` in the source field, and `Q₀` for the
Schur prime.  With `R_s ⊆ B'` (just proved), every prime `Q` of `B'` over `𝔪_A` has a centre
`Q ∩ R_s` on the Schur coordinate model, and:

* `B'/Q` is finite over `k(A)`, whose transcendence degree over `K` is `L − 1`; since
  `R_s/(Q ∩ R_s)` embeds in it, `dim R_s/(Q ∩ R_s) = L − 1`, i.e. **`ht (Q ∩ R_s) = 1`**;
* a height-one prime of the UFD `R_s` containing the irreducible `S` equals `(S)`, so if `S ∈ Q`
  then `Q ∩ R_s = (S)`;
* `(R_s)_{(S)}` is the source Schur valuation ring `B` (`criticalSchurSourceValuation_isLocalization`),
  and `B'_Q` is a valuation ring of the source field dominating it, hence equal to it;
* therefore `Q = Q₀`: **only the Schur prime is ramified**, which is `(D-1)`.

Only the transcendence-degree count is new work; everything else is already in the tree.

### The one mathlib gap that `(D-1)` and §3 both need, isolated

Everything in the `(D-1)` route above is corpus-side except one classical fact, which mathlib does
**not** have (checked: `Mathlib/RingTheory/Ideal/Height.lean` has no dimension formula, and there is
no `IsCatenary` development):

```text
height 𝔭 + dim (R ⧸ 𝔭) = dim R          for R a polynomial ring over a field
```

The only instance needed is the height-one case, and there it can be replaced by a direct
transcendence-degree computation, which the corpus is already equipped for (`Algebra.trdeg` is used
in `CorankTrdegRealizationLocus`, `ParameterCountTranscendenceBound`, …):

```text
trdeg_K (Frac (MvPolynomial (Fin L) K ⧸ (g)))  =  L − 1      for g irreducible
```

Proof to build: `g` involves some variable `x_i` nontrivially, so `x_i` is algebraic over the
others modulo `(g)`, giving `≤ L − 1`; and the remaining `L − 1` variables stay algebraically
independent, since a relation among them would be a nonzero element of `(g)` of degree zero in
`x_i`, impossible because `g` has positive degree in `x_i` and `MvPolynomial` is a domain.

With that in hand:

```text
trdeg k(A) = L − 1                              A is the local ring of a height-one prime
trdeg (R_s ⧸ (Q ∩ R_s)) = L − 1                 it embeds in a finite extension of k(A)
ht (Q ∩ R_s) = 1                                same computation, read backwards
Q ∩ R_s = (S)                                   height one containing the irreducible S
B'_Q = (R_s)_{(S)} = B                          a valuation ring dominating a DVR is that DVR
Q = Q₀                                          ** (D-1) **
```

and then §3's conormal argument runs at the unique ramified prime, giving `f_{Q₀} = 1`, and the
count `|collisionSupport| = e·f = 2` closes `(D)`.

### Correction and a found asset — half of the `(D-1)` dimension count is already available

A corpus search (do this before writing any dimension lemma) turns up an existing Krull-dimension
toolkit, and through it a mathlib lemma that was not obvious from the `Ideal.height` file:

```text
ringKrullDim_quotient_succ_le_of_nonZeroDivisor        (mathlib)
    ** dim (R ⧸ (a)) + 1 ≤ dim R  for a a non-zero-divisor **
ScalarExtendedHypersurfaceDimension.scalarExtendedHypersurface_krullDim_add_one_le
FiniteFamilyBlockHypersurfaceDimension, IteratedBlockHypersurfaceDimension
LocalizationAtPrimeDivisorDVR.ringKrullDim_localizationAtPrime
MvPolynomial.ringKrullDim_of_isNoetherianRing                              (mathlib)
```

So the **upper** half of the count is cheap: with `S` irreducible and `g ∉ (S)`, iterating the
quotient bound gives `dim (R_s ⧸ (S, g)) ≤ L − 2`.  What is still missing is the **lower** half,
i.e. that the centre of a place over the branch divisor is at least `(L−1)`-dimensional; that is
Krull's principal ideal theorem in the direction `dim (R ⧸ (f)) ≥ dim R − 1`, or equivalently the
statement that the Krull dimension of a finitely generated domain over a field equals its
transcendence degree.  Neither is in mathlib, and the corpus's `Algebra.trdeg` development does not
yet contain it either.  **That single statement is the whole remaining gap for `(D-1)`, and hence
for §3 and `(D)`.**

### Name-collision audit

A scan of all declarations added for this card against the rest of `HTGeometry` found exactly one
collision — `totalDegree_pderiv_lt`, already present in `PolynomialZeroSetDimension` (real
coefficients) — which would have broken the umbrella even though every module built in isolation.
Renamed to `totalDegree_pderiv_lt_of_ne_zero`; no other collisions among the 143 new declarations.

## Lean progress — the Krull dimension is an integral invariant (mathlib gap CLOSED)

```text
HTGeometry/IntegralExtensionKrullDim.lean                 (built)
    ringKrullDim_le_of_isIntegral        incomparability
    exists_primeChain_over               going up, for chains of ARBITRARY length
    le_ringKrullDim_of_isIntegral
    ringKrullDim_eq_of_isIntegral
        ** for an injective integral extension, dim R = dim S **
```

Mathlib has the two ingredients — `Ideal.IsIntegral.comap_lt_comap` (incomparability) and
`Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime` (one step of going up) — but neither the
chain version of going up (its own source marks that a `TODO`) nor the dimension statement.  The
chain version is proved by induction with `Fin.snoc`, using `Fin.strictMono_iff_lt_succ` so that
only consecutive comparisons have to be checked, and strictness at the top step comes from the two
contractions being distinct.

**What this unlocks.**  With Noether normalization (`exists_finite_inj_algHom_of_fg`, in mathlib)
this gives `dim A = s` for a finitely generated domain `A` over a field that is finite over
`MvPolynomial (Fin s) K`, i.e. **Krull dimension = transcendence degree**, which is exactly the
statement isolated above as the sole remaining gap for `(D-1)`.  The next step is to package that
corollary and then run the `(D-1)` chain:

```text
dim (R_s ⧸ 𝔭) = trdeg                       Noether normalization + the theorem just proved
trdeg (R_s ⧸ (Q ∩ R_s)) ≥ L − 1             it maps onto a subring of a finite extension of k(A)
dim (R_s ⧸ (S, g)) ≤ L − 2                  ringKrullDim_quotient_succ_le_of_nonZeroDivisor, twice
⟹ Q ∩ R_s = (S) ⟹ B'_Q = B ⟹ Q = Q₀        ** (D-1) **
```

## Lean progress — Krull dimension = transcendence degree

```text
HTGeometry/NoetherNormalizationKrullDim.lean              (built)
    ringKrullDim_eq_of_noetherNormalization
        ** dim R = s for any Noether normalization of R by s variables **
    exists_ringKrullDim_eq_of_finiteType
        every finitely generated algebra over a field has finite Krull dimension
```

Since the fraction field of a domain finite over `MvPolynomial (Fin s) k` is algebraic over
`k(X_0,…,X_{s-1})`, this **is** the statement that Krull dimension equals transcendence degree, and
it closes the gap isolated two sections above.  It rests on `ringKrullDim_eq_of_isIntegral` (proved
here) together with mathlib's Noether normalization and `MvPolynomial.ringKrullDim_of_isNoetherianRing`.

### `(D-1)` restated on the chart algebra, where the going-down instance already exists

The card's chain was written for `B' = integralClosure A E`, but the corpus's chart algebra `T` is
a better model, and the required height statement is already available there:

```text
R_s ⊆ T ⊆ E                       the Schur coordinates lie in T (adjoin of the coordinate set)
T is module-finite over Rs_o      criticalChartTowerFinite
Rs_o is integrally closed, T a domain  ⟹  going down holds
ht P = ht q' = 1                  for EVERY prime P of T lying over q'
                                  (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown,
                                   the same lemma already used for criticalSchurChartUnder_height)
```

So every point of the reduced fibre is a height-one prime of `T`, and `(D-1)` becomes: **the
Jacobian lies in only one of them**, i.e. `√(Jac)` is prime in `T`.  In `R_s` the corresponding
statement is true because `S` is irreducible in the UFD `R_s`; transporting it to `T` is the
remaining step, and the relation to use is
`criticalSourceReciprocalJacobian_det_eq_schurRamification`, which writes
`det Jac · scale^{2m} = ± aeval S` with `scale` a coordinate of `T`.

## Lean progress — every point of the reduced fibre is a divisorial point

```text
HTGeometry/CriticalSchurFibreHeight.lean                  (built)
    criticalSchurChartOverPrime_height_eq_one
        ** every prime of the chart algebra lying over the centre of the Schur place
           has height one **
```

Going down (the chart algebra is module-finite over the integrally closed chart ring) gives
`height P = height (P ∩ Rs_o) + (fibre height)`, and incomparability
(`Ideal.IsIntegral.mem_minimalPrimes_map_under`) makes the fibre height zero, since a prime lying
over the centre is minimal over the extended centre.

So the points of the reduced fibre **are** the height-one primes of the chart algebra above the
branch divisor, and the ramified ones are exactly those containing the Jacobian.  `(D-1)` is now the
single statement that only one height-one prime over the centre contains `Jac`; in the Schur
coordinate ring the corresponding fact holds because `S` is irreducible in a UFD, and the transport
is through `det Jac · scale^{2m} = ± aeval S`.

### `(D-1)` is now one classical input away, and the chain is fully determined

Let `P` be a height-one prime of the chart algebra `T` over the centre `q'` with `Jac ∈ P`, and
write `𝔭 = P ∩ R_s`.

1. **`S ∈ 𝔭`.**  `criticalSourceReciprocalJacobian_det_eq_schurRamification` reads
   `det Jac · scale^{2m} = ± aeval S`, and `scale` is the zeroth Schur coordinate, so it lies in
   `R_s ⊆ T`; hence `aeval S ∈ P`, i.e. `S ∈ 𝔭`.
2. **If `ht 𝔭 = 1` then `𝔭 = (S)`,** since `(S)` is a height-one prime of the UFD `R_s` contained
   in `𝔭`.
3. **Then `B ⊆ T_P`:** `B = (R_s)_{(S)} = (R_s)_𝔭 ⊆ T_P`.
4. **Hence `T_P = B`,** because a ring between a discrete valuation ring and its fraction field is
   one of the two, and `T_P` is local with nonzero maximal ideal.
5. **Hence `P = 𝔪_B ∩ T = P''`** — only one ramified prime, which is `(D-1)`.

Only step 2's hypothesis is missing, and it is the *same* classical statement as before, in its
sharpest form:

```text
ht 𝔭 + dim (R ⧸ 𝔭) = dim R          for R a polynomial ring over a field
```

Half of it is available: `ringKrullDim_quotient_succ_le_of_nonZeroDivisor` gives
`dim (R ⧸ 𝔭) + ht 𝔭 ≤ dim R` by iterating along a chain below `𝔭` (each step drops the dimension by
at least one).  The missing half is `dim (R ⧸ 𝔭) ≥ dim R − ht 𝔭`, i.e. that `R` is **catenary** —
equivalently, that a Noether normalization of `R ⧸ 𝔭` can be extended to one of `R`.  Everything
else on this card's `(D-1)` line is now proved.

## Lean progress — `(D-1)` IS CLOSED: the chart algebra is a localization of the Schur ring

The dimension-formula route recorded above was the wrong one, and the correction is worth stating
because it removes a classical input rather than supplying it.  The chart algebra `T` is **not
merely birational** to the Schur coordinate ring `R_s`: it is a *localization* of it, and that
makes the centre of every prime of `T` automatically a height-one prime of `R_s`.  No catenary
theory, no dimension formula, no Krull-dimension count is needed.

```text
HTGeometry/FiniteJetSubalgebraInversion.lean              (built)
    PolynomialCoefficientsInSubalgebra + closure lemmas
    adjoinSubalgebra_finiteReciprocalPositive_eq
    adjoinSubalgebra_finiteUnitSquarePositive_eq
    adjoinSubalgebra_finiteReciprocalSquarePositive_eq
        ** the finite jet transforms are invertible over the base RING, not just the base field **

HTGeometry/CriticalSchurCoordinateGeneration.lean         (built)
    criticalSourceNormalizedPositive_mem_adjoin_schur
    criticalSourceRaw_mem_adjoin_schur
    criticalSourceScale_pow_mul_recip_mem_adjoin_schur
        ** every raw coordinate is a polynomial in the Schur coordinates; every reciprocal
           coordinate becomes one after multiplying by a power of the scale **

HTGeometry/CriticalSchurChartClearing.lean                (built)
    criticalSchurClearingElement = scale^(n+2) * marked
    criticalSchurClearable                       the subalgebra of clearable elements
    criticalSourceChartAlgebra_mem_clearable
        ** every element of the chart algebra becomes a Schur polynomial after clearing a power
           of one explicit element **

HTGeometry/SubalgebraClearingPrime.lean                   (built)
    prime_subtype_of_clearing
        ** primality survives a denominator-clearing extension **

HTGeometry/CriticalSchurUniqueRamifiedPrime.lean          (built)
    eq_span_singleton_of_height_eq_one
    criticalSchurRamificationChartElement_prime
    criticalSchurChartPrime_eq_of_mem
        ** (D-1): every prime of the chart algebra over the centre containing the ramification
           element is the centre of the Schur place **
```

**Why it works.**  The Schur coordinates are the scale together with the normalized
reciprocal-square jet.  Both jet transforms — reciprocal and unit-square — are triangular with unit
leading terms, so in characteristic zero they are invertible over the base *ring*, with `2` the only
denominator; that is the content of `FiniteJetSubalgebraInversion`, which upgrades the corpus's
`IntermediateField.adjoin` statements to `Algebra.adjoin`.  Consequently every raw coordinate is a
polynomial in the Schur coordinates, and — by the cleared-numerator form of the reciprocal
coefficients — every reciprocal coordinate is one after dividing by a power of the scale.  The chart
ring inverts only the marked product, so with `w = scale^{n+2} · marked` (which lies in the Schur
ring, and is a unit of the chart algebra because `recip₀ = scale⁻¹` and the marked product is
inverted) the chart algebra is exactly `R_s[1/w]`.

The endgame is then three lines: the ramification element `S` is irreducible in the polynomial ring
`R_s`, `S ∤ w` because `S` is a nonunit of the chart algebra, hence `S` stays prime after clearing;
a height-one prime containing a prime element is generated by it; and both the given ramified prime
and the Schur centre are height-one primes containing `S`.

**State of `(D)`.**

```text
(R)    e ≥ 2 at the Schur place            ** DONE **
(D-e)  e = 2 exactly                       ** DONE **
(D-1)  a unique ramified prime             ** DONE **
(D-f)  f = 1                               steps 1-6 done; step 7 is the reduced-fibre dictionary
(D-c)  |collisionSupport| = e·f = 2        the same dictionary
```

### `(D-f)` step 7 and `(D-c)`, rewritten now that `(D-1)` is available

`(D-1)` removes the need for a general "reduced fibre ↔ residue embedding" dictionary.  The only
sheets that matter are the **singular** ones, and for those the dictionary is a two-line
consequence of `(D-1)`:

```text
σ a sheet whose reduced state is singular
  ⟹ det Jac ∈ σ⁻¹(𝔪_W)                    the reduced Jacobian determinant vanishes at z_σ
  ⟹ the prime σ⁻¹(𝔪_W) ∩ T over q' is ramified
  ⟹ (D-1): that prime is the Schur centre, i.e. σ⁻¹(W) = B
  ⟹ σ maps B into W and 𝔪_B into 𝔪_W, so it induces a residue embedding σ̄ : k(B) → k_W
```

With `σ̄` in hand everything reduces to statements already proved at the Schur place, because the
reduced data at `z_σ` is the `σ̄`-image of the reduced data at the Schur place:

```text
corner minor at z_σ  = σ̄ (residue_B (corner minor))  ≠ 0
        ⟹ corank one at EVERY singular reduced state, not just at the Schur place
conormal vector c₀   is defined over k(A), and every sheet fixes the observation field
        ⟹ the same vector c₀ lies in ker J(z_σ) for every singular σ
```

Since the conormal of a low tangent `(U,V)` is the *state-independent* linear expression
`(rev U, −rev V)` (`horizonConormalVector`), a one-dimensional kernel containing the fixed vector
`c₀` forces all collision tangents to be proportional; rescaling gives one common `(U,V)`, and
`criticalFibre_eq_of_shared_coprime_tangent` then identifies all singular reduced states.  That is
`f_{Q₀} = 1`.  The remaining count is the size of the one collapsing fibre, which is `e = 2`.

**Build order for the rest of `(D)`.**

```text
7a  σ⁻¹(W) = B for a singular sheet σ                    from (D-1)
7b  the induced residue embedding σ̄ and its compatibility with the fibre reduction
7c  corank one at every singular reduced state
7d  the fixed conormal vector lies in every such kernel
7e  all collision tangents proportional; rescale; criticalFibre_eq_of_shared_coprime_tangent
7f  f = 1, hence exactly one collapsing fibre
8   |collisionSupport| = e = 2, and the endgame theorem fires
```

## Lean progress — `(D-f)` steps 7a and 7c are CLOSED

```text
HTGeometry/CriticalSheetChartIntegrality.lean             (built)
    sheet_mem_normalClosureSchur_of_observationRange
    criticalSourceRaw_sheet_mem_normalClosureSchur
    criticalSourceRecip_sheet_mem_normalClosureSchur
    algebraMap_chartRing_mem_observationRange
    criticalSourceChartAlgebra_sheet_mem_normalClosureSchur
        ** every sheet maps the chart algebra into the normal-closure Schur valuation ring **

HTGeometry/CriticalSheetSchurPullback.lean                (built)
    criticalSheetChartToNormalSchur      the sheet as a map of the chart algebra
    criticalSheetChartPrime              the pulled-back centre, prime and over q'
    criticalSheetChartPrime_eq_of_singular
        ** (D-1) applied to sheets: a SINGULAR sheet pulls the Schur place back to itself **
    criticalSheetSourceSchurLift         hence a lift B → W of the sheet
    criticalSheetSourceSchurLift_coe     whose underlying map is the sheet
    residue_criticalSheetSourceSchurLift_ne_zero

HTGeometry/CriticalSheetJacobianCorankOne.lean            (built)
    criticalSheetSourceSchurLift_mem_maximalIdeal    the lift is local
    criticalSheet_finrank_ker_reduced_jacobian_eq_one
        ** corank one at EVERY singular point of the reduced fibre **
```

The mechanism is worth recording: a sheet `σ` whose reduced state is singular has
`det Jac ∈ σ⁻¹(𝔪_W)`, so the prime `σ⁻¹(𝔪_W) ∩ T` of the chart algebra lies over the branch centre
*and* contains the ramification element; `(D-1)` then forces it to be the centre of the Schur place.
Since the source Schur valuation ring is the localization of the chart algebra at that centre,
`IsLocalization.lift` produces a ring map `B → W` whose underlying map is `σ` itself, and it is
local because the centre is exactly the contracted maximal ideal.  Nonvanishing residues therefore
transfer, and the corner-minor computation at the Schur place applies verbatim at every singular
reduced state.

**State of `(D-f)` step 7.**

```text
7a  σ⁻¹(W) = B for a singular sheet σ                    ** DONE **
7b  compatibility of the lift with the fibre reduction   NEXT
7c  corank one at every singular reduced state           ** DONE **
7d  the fixed conormal vector lies in every such kernel
7e  all collision tangents proportional; rescale
7f  f = 1, hence exactly one collapsing fibre
8   |collisionSupport| = 2, and the endgame theorem fires
```

## Lean progress — `(D-f)` steps 7b and 7d are CLOSED

```text
HTGeometry/CriticalSheetConormalVector.lean               (built)
    criticalSheetSourceSchurLift_algebraMap_observation
        the lift agrees with the canonical map on the observation valuation ring
    criticalNormalSchurConormalVector          one vector, independent of the sheet
    criticalSheet_jacobian_mulVec_conormal
        ** it lies in the kernel of the reduced Jacobian at EVERY singular sheet **
    exists_criticalNormalSchurConormalVector_ne_zero

HTGeometry/CriticalSheetReducedJacobian.lean              (built)
    horizonObservationJacobian_map              functoriality of the horizon Jacobian
    criticalObservationJacobian_eq_horizon      the corpus Jacobian IS the horizon Jacobian
    criticalSheet_recipPolynomialIntegral_map   the reduced reciprocal jet of a sheet
    criticalSheet_jacobian_eq_horizon
        ** the reduced observation Jacobian at a singular sheet is the horizon Jacobian of that
           sheet's reduced reciprocal jet **
```

Combined with corank one (7c) this says: at every singular reduced state the kernel of the horizon
Jacobian is the line spanned by one fixed vector `c₀` coming from the observation side.

**What is left, precisely.**

```text
7e  a collision forces its sheet to be singular
      det (horizon Jacobian at z_σ) = 0 because the conormal of a nonzero tangent is a nonzero
      kernel vector; and det (horizon Jacobian Y) = ± det (reciprocal Jacobian Y), whose σ-image
      is ± σ(aeval S) · σ(scale)^{-2m} with σ(scale) a unit — so σ is singular in the sense of
      CriticalSheetSchurPullback.
7f  two collisions have the same reduced state
      both conormals span the same line as c₀, so the tangents are proportional; rescale and apply
      criticalFibre_eq_of_shared_coprime_tangent.  That is f_{Q₀} = 1.
8   |r⁻¹(z₀)| = 2
      the only genuinely missing classical input: the number of sheets over one reduced state is
      the ramification index, which is 2 by (D-e).  In the corpus's terms this is the statement
      that sheets inducing the same residue embedding differ by an inertia element, together with
      |I| = e = 2 (tame, characteristic zero).
```

Everything before item 8 is corpus wiring of theorems that are now all in the tree.

## Lean progress — the singularity criterion and the kernel leading coefficient

```text
HTGeometry/HorizonJacobianDeterminant.lean                (built)
    criticalReciprocalJacobian_map               functoriality
    horizonObservationJacobian_eq_fromBlocks
    det_horizonObservationJacobian
        ** det of the horizon Jacobian = det of the reciprocal Jacobian **
    horizonConormalVector_ne_zero                a nonzero tangent has a nonzero conormal

HTGeometry/CriticalSheetSingularity.lean                  (built)
    criticalSheetReducedRecipPolynomial          the reduced jet of a sheet
    criticalSheetFibre_recipPolynomial_map
    det_criticalReciprocalJacobian_criticalSheetReducedRecipPolynomial
    subtype_det_criticalReciprocalJacobian_sheet
    criticalSourceJacobianDetChart
    criticalSchurRamificationChartElement_dvd
    criticalSheet_singular_of_det_eq_zero
        ** a degenerate reduced Jacobian makes the sheet singular, hence (D-1)-controlled **

HTGeometry/MatrixKernelDeletedColumn.lean                 (built)
    ker_coord_ne_zero_of_det_submatrix_ne_zero
        ** a kernel vector is nonzero at the deleted column **
```

The last item is what gives `U(0) ≠ 0` for a collision tangent: the surviving minor of the
observation Jacobian deletes the last raw column, whose conormal coordinate is exactly `U(0)`.
With `U(0) ≠ 0` and `V ≡ −Y²U` the corpus's `isCoprime_of_low_tangent_unique` supplies coprimality,
and `criticalFibre_eq_of_shared_coprime_tangent` then collapses the singular reduced states.

### Session bookkeeping — modules landed for `(D-1)` and `(D-f)`

All of the following are in the tree, wired into `HTGeometry.lean`, and free of `sorry`, `admit`,
`axiom`, `opaque` and `unsafe`:

```text
CoordinatePrefixPrimeChain          DegreeOnePolynomialQuotient
DegreeOneHypersurfaceDimension      FiniteJetSubalgebraInversion
CriticalSchurCoordinateGeneration   SubalgebraClearingPrime
CriticalSchurChartClearing          CriticalSchurUniqueRamifiedPrime     ** (D-1) **
CriticalSheetChartIntegrality       CriticalSheetSchurPullback           ** 7a **
CriticalSheetJacobianCorankOne      ** 7c **      CriticalSheetConormalVector   ** 7d **
CriticalSheetReducedJacobian        ** 7b **      HorizonJacobianDeterminant
CriticalSheetSingularity            MatrixKernelDeletedColumn
```

The remaining assembly (`criticalSchur_reducedFibre_eq_of_collisions`) chains them as follows, and
each link is a theorem already in the tree:

```text
collision (σ,τ)                     criticalSchur_exists_reduced_tangent_of_collision
  ⟹ nonzero low tangent (U,V)
  ⟹ nonzero conormal                horizonConormalVector_ne_zero
  ⟹ det of the horizon Jacobian = 0 Matrix.exists_mulVec_eq_zero_iff + det_horizonObservationJacobian
  ⟹ σ is singular                   criticalSheet_singular_of_det_eq_zero
  ⟹ corank one at z_σ               criticalSheet_finrank_ker_reduced_jacobian_eq_one   (via (D-1))
  ⟹ (U,V) ∝ the fixed conormal      criticalSheet_jacobian_mulVec_conormal + exists_smul_…
  ⟹ U(0) ≠ 0                        ker_coord_ne_zero_of_det_submatrix_ne_zero
  ⟹ V(0) ≠ 0                        dvd_reciprocal_of_low_tangent
  ⟹ (U,V) coprime                   isCoprime_of_low_tangent_unique
  ⟹ both reduced states equal       criticalFibre_eq_of_shared_coprime_tangent
```

That is `f_{Q₀} = 1`.  The one classical input still outstanding for `(D)` is item 8 of the build
order: the fibre of the reduction over that single point has exactly `e = 2` elements.

### Item 8 has a mathlib backbone — the route to `(D-c)`

The one classical input still missing is the count of sheets over a single reduced state.  Mathlib
already carries the hard half, in `Mathlib/NumberTheory/RamificationInertia/Galois.lean`:

```text
Ideal.card_stabilizer_eq
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S
Ideal.card_inertia_eq_ramificationIdxIn
    Nat.card (P.inertia G) = p.ramificationIdxIn S
```

for a Galois group action with `Module.Finite`, `Flat` and a perfect residue field — all satisfied
here (characteristic zero).  The route is therefore:

```text
8a  S := integral closure of A in the normal closure N; it is Dedekind, module-finite and flat
8b  P := the prime of S under the chosen valuation W;  stabilizer G P = the decomposition group
8c  card_stabilizer_eq gives |D| = e(W/A) · f(W/A)
8d  sheets ≅ G / Gal(N/E); the sheets σ with σ⁻¹(W) = B are the classes in D·Gal(N/E)
8e  |D · Gal(N/E) / Gal(N/E)| = |D| / |D ∩ Gal(N/E)| = e(B/A) · f(B/A) = 2 · 1 = 2
8f  every colliding sheet is singular (proved), and every singular sheet has σ⁻¹(W) = B by (D-1),
    so collisionSupport has at most 2 elements — which is (D)
```

Steps `8a`–`8c` are mathlib instantiation; `8d`–`8e` are the coset bookkeeping; `8f` is already in
the tree.  Note that this route needs `(D-e)` (`e(B/A) = 2`, proved) and `(D-f)` (`f(B/A) = 1`).

## Lean progress — `(D-f)` IS CLOSED

```text
HTGeometry/CriticalSheetFixedConormal.lean                (built)
    criticalSchurFixedConormal                one nonzero conormal vector for all sheets
    criticalSheet_horizonJacobian_mulVec_fixedConormal
    criticalSheet_finrank_ker_horizonJacobian
    criticalSheet_reduced_inv
    criticalSheet_exists_smul_of_tangent
        ** every low tangent at a singular sheet is a multiple of that vector **

HTGeometry/CriticalSheetCollisionTangent.lean             (built)
    criticalSheet_singular_of_tangent
    criticalSheetReducedRecipPolynomial_coeff_zero_ne_zero
    criticalSheet_tangent_coeff_zero_ne_zero      ** U(0) ≠ 0 **

HTGeometry/CriticalSchurUniqueCollisionPoint.lean         (built)
    criticalNormalClosureSchurResidue_charZero
    criticalSheet_tangent_smul                    tangents at two singular sheets are proportional
    criticalSheet_tangent_recip_coeff_zero_ne_zero
    criticalSheet_tangent_isCoprime
    criticalSchur_exists_reduced_tangent_of_collision'
    criticalSchur_reducedFibre_eq_of_collisions
        ** (D-f): ALL COLLISIONS OF THE SCHUR REDUCTION HAPPEN AT ONE POINT **
```

The statement proved is exactly what `(D)` needs on the "how many collision points" side:

```text
σ ≠ τ,  r σ = r τ,  σ' ≠ τ',  r σ' = r τ'   ⟹   r σ = r σ'
```

**State of `(D)`.**

```text
(R)    e ≥ 2 at the Schur place            ** DONE **
(D-e)  e = 2 exactly                       ** DONE **
(D-1)  a unique ramified prime             ** DONE **
(D-f)  one collision point                 ** DONE **
(D-c)  that point carries exactly 2 sheets   the last classical input (item 8 above)
```

## Lean progress — `(D)` is now one count away

```text
HTGeometry/CriticalSchurCollisionSupportFibre.lean        (built)
    criticalSchur_collisionSupport_reducedFibre_eq
        ** the whole collision support sits over ONE point of the reduced fibre **
    criticalSchur_collisionSupport_ncard_le_two_of_fibre
        ** if that one fibre carries at most two sheets, |collisionSupport| ≤ 2 **
```

So the entire card now rests on one statement, stated in Lean and consumed by the theorem above:

```text
∀ σ,  ncard {τ | r τ = r σ}  ≤  2
```

i.e. the Schur reduction is at most two-to-one.  Two routes are available, both classical:

* **Inertia orbit.**  Two sheets with the same reduced state differ by an element of the inertia
  group of the chosen normal-closure Schur place, and the inertia orbit of a singular sheet has
  size `e(B/A) = 2` by `(D-e)`.  The corpus already has the inertia group
  (`criticalSchurInertiaGroup`), its faithful action on sheets
  (`criticalSchurInertiaAction_injective`) and tame cyclicity (`isCyclic_of_tame`); mathlib has
  `Ideal.card_inertia_eq_ramificationIdxIn` for the ideal-theoretic count.
* **Root multiplicity.**  A singular sheet is a local `A`-algebra map `B → W`
  (`criticalSheetSourceSchurLift`), hence a root in `W` of the minimal polynomial of a generator,
  congruent to a fixed residue; the number of such roots is at most the multiplicity of that
  residue in the reduction, which is `e f = 2`.

Everything else on this card — `(R)`, `(D-e)`, `(D-1)`, `(D-f)`, and the whole of §2's conormal
apparatus — is now Lean-proved and unconditional.

## Lean progress — the ramification dictionary at an ARBITRARY base field

The card's `(D4)` — `∀ σ, ncard {τ | r τ = r σ} ≤ 2` — was traced to one missing piece: the identity
`|Stab_I(σ)| = e(w / O_σ)` for the *intermediate* field `σ(F_src)`, not just for the observation
field.  Everything else in the endgame follows from it (see the route recorded in
`_FORMALIZATION-LEDGER.md`, together with the two dead ends that were checked and rejected: the
different is uninformative about `e(w/Q₀)`, and pure orbit combinatorics of a faithful cyclic action
with `Σ orbit ≤ 1 + t` does not force `t = 1` — `t = 20`, orbits `{8,10}` survives every count).

Two modules landed, both `lake build`-green and `#print axioms = [propext, Classical.choice,
Quot.sound]`.

```text
HTGeometry/TameInertiaOrderBound.lean
    smul_pow_eq
    residueRatioHom_pow_eq_one_of_smul_eq   a fixed `x = π^n·u` forces `ratio(g)^n = 1`
    natCard_le_of_smul_eq_of_eq_pow_mul     ** |Γ| ≤ n **
    natCard_le_addVal_of_smul_eq            ** |Γ| ≤ addVal W x for every fixed nonzero nonunit **

HTGeometry/ValuationSubringInertiaDictionary.lean
    smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup
    toValuationSubring, centerPrime, centerPrime_isPrime, centerPrime_ne_bot
    isUnit_toValuationSubring_of_notMem, inv_mem_of_notMem_centerPrime
    mem_maximalIdeal_of_mul_eq
    centerHeightOne
    valuationSubringAtPrime_eq   ** W IS the localization of S at its centre **
    mem_iff_exists_div           ** x ∈ W ↔ x = a/s with a s : S and s off the centre **
    notMem_centerPrime_smul, smul_valuationSubring_eq, toDecomposition
    smul_sub_mem_maximalIdeal
    toDecomposition_mem_inertiaSubgroup, coe_mem_inertia_of_mem_inertiaSubgroup
    inertia_eq_map               ** ideal inertia = valuation inertia, as subgroups of Gal(L/F) **
    natCard_inertia_eq_natCard_inertiaSubgroup
```

**What the first module is for.**  It is the *cheap* half of `|I| = e`.  A tame action on a DVR has
an injective ratio character `Γ → k^×` (`TameInertiaCyclic`); if `Γ` fixes an element of divisorial
order `n`, the character lands in `μ_n`, and a field has at most `n` `n`-th roots of unity.  Applied
to the image of a uniformizer of a `Γ`-fixed subfield this reads `|I_M| ≤ e(w/M)` with no ideal
theory at all.  It also gives, for free, the fact the card needs in step 2: **a sheet fixed by the
whole inertia group is unramified** — take `x = σ(π_{O_σ})`, which `I` fixes, and get
`|I| ≤ e(w/O_σ) = |I|/e(O_σ/A)`, i.e. `e(O_σ/A) = 1`.

**What the second module is for.**  It is the *expensive* half, and it is stated at an arbitrary
base field `F` of the normal extension, which is exactly what the corpus's existing
`CriticalSchurIntegralClosurePlace` + `CriticalSchurIdealInertiaTransport` pair is **not** — those
are hard-wired to the observation field, so they cannot see `Stab_I(σ)`.

Its engine is `mem_iff_exists_div`.  mathlib has
`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`, the localization of a Dedekind domain
at a height-one prime, with `Ring.KrullDimLE 1` and `IsLocalization` instances already attached; a
valuation subring of Krull dimension one below a *proper* valuation subring equals it
(`ValuationSubring.eq_of_le_of_ne_top`).  So `W` is literally `S` localized at its centre, and
membership in `W` is "a fraction with denominator off the centre".  With that, both inclusions
become one-line computations:

```text
g • (a/s) = (g•a)/(g•s)                            and    g•s ∉ P because g•s − s ∈ P
(g•a)s − a(g•s) = (g•a − a)s − a(g•s − s) ∈ P      with denominator (g•s)s off P
```

so ideal inertia stabilises `W` and kills residues; conversely a valuation-inertia element `g`
sends every `x : S` to `g•x − x` whose image in `W` is in the maximal ideal, i.e. `g•x − x ∈ P`.
The two subgroups of `Gal(L/F)` are therefore *equal*, not merely comparable — the corpus only had
the injection, and only at the bottom field.

**Effect on the card.**  Combined with mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` this is
`|W.inertiaSubgroup F| = e` for every `F` over which `L` is Galois.  The remaining work on `(D4)`
is instantiation, not new mathematics:

```text
(1) O_σ := W.comap σ is a DVR                    valuationSubringComap_isDiscreteValuationRing
                                                 (already in the tree)
(2) |Stab_I(σ)| = |W.inertiaSubgroup (σ F_src)|  restriction of scalars, definitional
(3) |I| = e(w/A), |Stab_I(σ)| = e(w/O_σ)         the two modules above + mathlib
(4) orbit_σ = e(O_σ/A)                           Ideal.ramificationIdx_tower
(5) O_σ = O_src for σ in the collision fibre     the Schur coordinate ring is a POLYNOMIAL ring,
                                                 so every height-one localization is a DVR and the
                                                 valuation ring is determined by the residues of
                                                 the coordinates — which two colliding sheets share
(6) e(O_src/A) = 2                               criticalSchur_source_ramificationIdx_eq_two
(7) all orbits ≤ 2 ⟹ |I| ≤ 2                     CyclicCollisionOrderBound.natCard_le_two_of_isCyclic
(8) |F| ≤ 1 + v_w(f'(θ)) = 2                     RootCongruenceValuationCount + monogenicity +
                                                 criticalSchur_differentIdeal_not_le_sq
```

## Lean progress — `|inertia| = e` at an arbitrary base field is PROVED

`HTGeometry/ValuationInertiaRamificationIndex.lean` (wired, built, axiom-clean)

```text
integralClosure_mem_of_base_mem
    the integral closure of the base sits inside any valuation subring containing the base
natCard_inertiaSubgroup_eq_ramificationIdxIn
    ** Nat.card (W.inertiaSubgroup F) = ramificationIdxIn (maximalIdeal R) (integralClosure R L) **
```

for a discrete valuation ring `R` with fraction field `F`, a finite Galois `L/F`, and a valuation
subring `W ⊆ L` containing `R`, not equal to `L`, and with at least one nonzero element of `R` a
nonunit of `W`.  That last hypothesis is what makes `W` lie over the maximal ideal of `R` rather
than over zero, and it is the only "nondegeneracy" input.

This is the statement the card has been missing.  The corpus already had `|I| = e` **at the
observation field** (`natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn`), but that
development is hard-wired to `criticalObservationField`, so it says nothing about
`Stab_I(σ) = W.inertiaSubgroup (σ F_src)`, which is the group whose order controls the orbit of a
sheet.  The new statement is uniform in the base field, so it applies to every sheet at once.

Two implementation traps, recorded:

* the `Gal(L/F)`-action on `integralClosure R L` must be introduced with `letI`, not `haveI` —
  `algebraMap_galRestrict_apply` is a statement about `galRestrict`, and only a `let`-bound instance
  lets `g • x` unfold to it (see [[haveI-inferinstance-opaque-trap]]);
* `Module.Flat R (integralClosure R L)` is found only after the torsion-free instance, which comes
  from injectivity of `R → integralClosure R L` through `L`.

**What remains for `(D4)`, exactly.**  With `|I_M| = e(w/M)` in hand for every intermediate `M`, the
orbit of a sheet is `e(O_σ/A)` and everything reduces to arithmetic of `addVal W`, because

```text
addVal W (π_A) = e(O_σ/A) · addVal W (π_{O_σ})
```

is pure valuation additivity (a unit of `O_σ` is a unit of `W`).  The one remaining general lemma is
therefore the numeric bridge

```text
ramificationIdxIn (maximalIdeal R) (integralClosure R L) = addVal W (algebraMap R L π_R)
```

whose proof is mathlib's `ramificationIdx_def` (`ramificationIdx = length (Sq ⧸ 𝔪_R Sq)`) plus
`IsDiscreteValuationRing.length_quotient_pow_maximalIdeal` (`length (W ⧸ 𝔪_W^n) = n`), transported
along the localization identification `Localization.AtPrime (centerPrime) ≃ W` that
`valuationSubringAtPrime_eq` already provides.  After that the card's `(D4)` is instantiation only.

## Lean progress — the orbit formula is now assembled from general theorems

Two more pieces landed, both `lake build`-green and axiom-clean.

```text
HTGeometry/ValuationInertiaIntermediateField.lean
    mem_inertiaSubgroup_iff        g is inertial ⟺ g•y − y ∈ 𝔪_W for every y : W
    decompositionRestrict, coe_decompositionRestrict, decompositionRestrict_smul
    mem_inertiaSubgroup_decompositionRestrict
    natCard_inertiaSubgroup_intermediate
        ** |W.inertiaSubgroup M| = #{ g inertial over F : g fixes M pointwise } **

HTGeometry/ValuationInertiaRamificationIndex.lean   (extended)
    liesOver_centerPrime           the centre lies over the prescribed maximal ideal
    ramificationIdxIn_tower
        ** ramificationIdxIn p T = Q.ramificationIdx A * ramificationIdxIn Q T **
```

The first rests on a single `rfl`: the pointwise action of `g : L ≃ₐ[M] L` on a valuation subring of
`L`, and on `W` itself, is the action of `g.restrictScalars F`, because it only reads the underlying
ring map.  So the stabiliser of a sheet `σ` inside the inertia group of the observation field *is*
the inertia group of `σ(F_src)` — no comparison lemma, an equality of conditions.

The second is the multiplicativity that the card needs, and it is stated with **no Galois hypothesis
on the middle extension**.  That matters: `F_src/E` is precisely the non-normal step, so mathlib's
`Ideal.ramificationIdxIn_mul_ramificationIdxIn` — which assumes `IsGaloisGroup` for the middle — is
unusable and must not be reached for.  `Ideal.ramificationIdx_tower` between two applications of
`ramificationIdxIn_eq_ramificationIdx` is the right instrument.

**Consequence.**  For every sheet `σ`, writing `A` for the observation Schur DVR, `M_σ = σ(F_src)`,
`B_σ` for the integral closure of `A` in `M_σ` and `Q_σ` for the prime of `B_σ` under `w`:

```text
|I|                      = ramificationIdxIn 𝔪_A  C          (ValuationInertiaRamificationIndex)
|Stab_I(σ)| = |W.inertiaSubgroup M_σ| = ramificationIdxIn Q_σ C   (idem, + IntermediateField)
|I|                      = e(Q_σ/𝔪_A) · |Stab_I(σ)|          (ramificationIdxIn_tower)
```

so **the `I`-orbit of a sheet has exactly `e(Q_σ/𝔪_A)` elements**, unconditionally.  Every step of
`(D4)` above the concrete instantiation is now a theorem in the tree.  What is left is bookkeeping
with the horizon's own objects: exhibit the instances (`B_σ` Dedekind, `IsIntegralClosure C B_σ L`,
the two `hcent` conditions), identify `σ⁻¹(W)` with the source Schur valuation ring for a colliding
sheet, and read `e = 2` off `criticalSchur_source_ramificationIdx_eq_two`.

## Lean progress — the sheet stabiliser is an inertia group, and the orbit criterion

```text
HTGeometry/CyclicOrbitOrderBound.lean            (wired, built, axiom-clean)
    sq_smul_eq_self_of_orbit_le_two
    natCard_le_two_of_isCyclic_of_orbit
        ** faithful + cyclic + every orbit of size ≤ 2  ⟹  |G| ≤ 2 **

HTGeometry/CriticalSheetStabilizerInertia.lean   (wired, built, axiom-clean)
    criticalNormalClosureAction_eq_self_iff   a sheet is fixed ⟺ its field range is fixed
    criticalSchurInertiaGroup_eq              the corpus's inertia group IS the valuation one
    criticalSchurInertiaAction_apply
    natCard_sheetStabilizer_eq_natCard_inertiaSubgroup
        ** |Stab_I(σ)| = |W.inertiaSubgroup (AlgHom.fieldRange σ)| **
```

`CyclicCollisionOrderBound` bounded the inertia group through the *fibres* of the reduction; the
ramification dictionary delivers *orbits* instead, so the orbit form is what the endgame now needs.

Two elaboration traps recorded, because they cost a rebuild each: the critical field stack times out
the default instance budget (raise `synthInstance.maxHeartbeats`, `maxHeartbeats`,
`maxSynthPendingDepth`), and the final step must **not** be a `rw` — computing the motive for
`natCard_inertiaSubgroup_intermediate` exhausts the `isDefEq` budget, while `Eq.trans` against the
same lemma costs nothing.

**State of `(D4)`.**  Every general theorem the route needs is now in the tree:

```text
|Stab_I(σ)| = |W.inertiaSubgroup (fieldRange σ)|              DONE (this entry)
|W.inertiaSubgroup F| = ramificationIdxIn p T, any base F     DONE
ramificationIdxIn p T = e(Q/p) · ramificationIdxIn Q T        DONE
faithful + cyclic + orbits ≤ 2 ⟹ |I| ≤ 2                      DONE (this entry)
```

What is left is the instantiation of the middle two on the horizon's own rings — the observation
Schur DVR at the bottom and `integralClosure A (fieldRange σ)` in the middle — plus
`σ⁻¹(W) = criticalSchurSourceValuationSubring` for a colliding sheet and the derivative count.

## Lean progress — `|I| = e` is now an EQUALITY on the horizon's own rings

```text
HTGeometry/ValuationInertiaRamificationIndex.lean   (extended)
    natCard_inertiaSubgroup_eq_ramificationIdx_mul
        ** |W.inertiaSubgroup F| = e(Q/p) · |W.inertiaSubgroup M| **   — the orbit formula

HTGeometry/CriticalSchurInertiaRamificationIndex.lean   (wired, built, axiom-clean)
    ValuationSubring.ne_top_of_isDiscreteValuationRing
    criticalSchurNormalBase_algebraMap_mem, criticalSchurNormalBase_centre
    natCard_criticalSchurInertiaGroup_eq_ramificationIdxIn
        ** Nat.card (criticalSchurInertiaGroup) = ramificationIdxIn 𝔪_A (normal integral closure) **
```

The last statement is new content, not a repackaging: the corpus previously owned only the
*injection* (`criticalSchurIdealInertiaToInertia_injective` together with
`natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn`), i.e. `e ≤ |I|`.  The orbit of a
sheet is `|I|` divided by the order of its stabiliser, so both numbers have to be computed, not
bounded, and the equality is what makes that possible.

**Remaining for `(D4)`, in order.**

```text
(a) IsIntegralClosure T B_σ L for B_σ = integralClosure A (fieldRange σ)   transitivity of integrality
(b) Q_σ := comap of 𝔪_W to B_σ; prime, nonzero, hence maximal              Dedekind
(c) instantiate natCard_inertiaSubgroup_eq_ramificationIdx_mul at (E, A) and (fieldRange σ, B_σ)
        ⟹ orbit_σ = e(Q_σ / 𝔪_A)
(d) σ⁻¹(W) = criticalSchurSourceValuationSubring for a colliding sheet     polynomial-ring argument
(e) e(Q_σ/𝔪_A) = 2                                    criticalSchur_source_ramificationIdx_eq_two
(f) natCard_le_two_of_isCyclic_of_orbit                ⟹ |I| ≤ 2
(g) the derivative count                               ⟹ |collisionSupport| ≤ 2
```

Nothing in (a)–(g) is research mathematics; it is the bookkeeping that the general theorems were
built to make possible.

## Lean progress — THE ORBIT FORMULA IS A THEOREM ON THE HORIZON

```text
HTGeometry/ValuationInertiaIntermediateBase.lean   (wired, built, axiom-clean)
    intermediateBaseToTop, intermediateBase_mem, intermediateToW, intermediateCentre
    mem_intermediateCentre_iff, liesOver_intermediateCentre, intermediateCentre_ne_bot
    natCard_inertiaSubgroup_eq_intermediate_mul
        ** |W.inertiaSubgroup F| = e(Q_M / p) · |W.inertiaSubgroup M| **, general

HTGeometry/CriticalSheetOrbitRamification.lean     (wired, built, axiom-clean)
    criticalNormalClosure_isGalois
    charZero_residueField_of_ringHom, criticalIntermediateCentre_charZero
    natCard_criticalSchurInertiaGroup_eq_intermediate_mul
    natCard_criticalSchurInertiaGroup_eq_sheet_mul
        ** |I| = e(Q_σ / 𝔪_A) · |Stab_I(σ)| **, for every geometric sheet σ
```

So **the `I`-orbit of a sheet has exactly `e(Q_σ / 𝔪_A)` elements**, where `Q_σ` is the place `σ`
cuts out on the integral closure of the observation Schur DVR inside `AlgHom.fieldRange σ`.  This is
the statement the card has been reaching for since the tame-inertia entry: a sheet is moved by
inertia exactly when its place ramifies, and its orbit has as many members as the ramification index.

Nothing in it assumes the source field is normal over the observation field — which is the whole
point, and the reason `Ideal.ramificationIdxIn_mul_ramificationIdxIn` (which does assume it) had to
be replaced by `Ideal.ramificationIdx_tower` between two applications of the dictionary.

**Immediate consequence, free of further work.**  Inertia preserves the reduced fibre label
(`criticalGeometricSheetToSchurReducedFibre_inertia_invariant`), so an orbit lies inside one fibre;
hence a sheet outside the collision support is fixed by all of `I`, and therefore
`e(Q_σ / 𝔪_A) = 1` for it.  Ramification of the horizon is *concentrated on the collision support*.

**What is left, exactly.**

```text
(d) e(Q_σ / 𝔪_A) = 2 for a colliding sheet.  Route: σ⁻¹(W) has the same centre on the Schur
    COORDINATE RING as the canonical sheet, because both reduce the coordinates to the same
    residues; that ring is a polynomial ring, so its height-one localization is a DVR, and a
    valuation ring containing a DVR with the same fraction field is that DVR.  Then
    criticalSchur_source_ramificationIdx_eq_two.
(e) natCard_le_two_of_isCyclic_of_orbit + isCyclic_of_tame  ⟹  |I| ≤ 2.
(f) RootCongruenceValuationCount + monogenicity + criticalSchur_differentIdeal_not_le_sq
    ⟹ |collisionSupport| ≤ 2, which is (D4).
```

## Lean progress — ramification is concentrated on the collision support

```text
HTGeometry/CriticalSheetUnramifiedOutsideCollision.lean   (wired, built, axiom-clean)
    nat_eq_one_of_eq_mul_self
    criticalSchurInertiaAction_eq_self_of_notMem_collisionSupport
        ** a sheet outside the collision support is fixed by the whole Schur inertia group **
    criticalSheetRamificationIdx_eq_one_of_notMem_collisionSupport
        ** and therefore sits over an UNRAMIFIED place **
```

This is the first genuinely arithmetic consequence of the orbit formula, and it runs in the useful
direction: the *geometric* statement that two sheets collide has become the *arithmetic* statement
that a place ramifies.  Every ramified sheet is a colliding sheet, so bounding the collision support
and bounding the total ramification are the same problem — which is what the different was always
supposed to control, and what `criticalSchur_differentIdeal_not_le_sq` supplies at the Schur place.

Ten modules landed for this card on 2026-08-22, every one `lake build`-green with
`#print axioms = [propext, Classical.choice, Quot.sound]`.

## Lean progress — the inertia order is bounded by the sheet ramification

```text
HTGeometry/CyclicRepStabilizerBound.lean          (wired, built, axiom-clean)
    repStabilizer, mem_repStabilizer
    natCard_le_two_of_isCyclic_of_stabilizer_card
        ** |G| ≤ 2·#{g : ρ g x = x} for every x  ⟹  |G| ≤ 2 **

HTGeometry/CriticalSchurInertiaCyclic.lean        (wired, built, axiom-clean)
    criticalSchurInertia_faithfulSMul, criticalSchurUpperResidue_charZero
    isCyclic_criticalSchurInertiaGroup            ** the Schur inertia group is CYCLIC **

HTGeometry/CriticalSchurInertiaOrderBound.lean    (wired, built, axiom-clean)
    natCard_criticalSchurInertiaGroup_eq_sheet_mul'
    natCard_criticalSchurInertiaGroup_le_two_of_ramification
        ** every sheet over a place of ramification index ≤ 2  ⟹  |I| ≤ 2 **
```

`TameInertiaCyclic.isCyclic_of_tame` had never been instantiated; it is now, on the horizon's own
upper Schur place.

**Elaboration discipline, recorded because it cost a dozen rebuilds.**  On the horizon's sheet and
permutation types every `rw`, `show`, `change`, and every unfolding of `MulAction.stabilizer` or
`MulAction.orbit`, exhausts the elaborator — a `rw` must compute a motive over those types, and
`MulAction.compHom` plus `SetLike` membership is several unfolds deep.  The same statement phrased
with `MulAction.orbit` does not elaborate at twenty million heartbeats; phrased as a cardinality
inequality of naturals over a plain subtype it takes seconds.  So: **state every group-theoretic
step abstractly, give its hypothesis as a `Nat.card` inequality over a plain subtype, and
instantiate with `Eq.trans_le`, never `rw`.**

**`(D4)` now rests on one statement.**

```text
∀ σ,  e(Q_σ / 𝔪_A) ≤ 2
```

Everything else is proved: the orbit formula, cyclicity, faithfulness, the order bound, and the fact
that sheets outside the collision support are unramified.  For a sheet *inside* the collision
support the route is `σ⁻¹(W) = criticalSchurSourceValuationSubring` — two sheets with the same
reduced fibre label reduce every Schur coordinate to the same residue, so they have the same centre
on the Schur coordinate ring, which is a polynomial ring, so that centre's localization is a DVR and
`ValuationSubring.eq_of_le_of_ne_top` identifies the two valuation rings — followed by
`criticalSchur_source_ramificationIdx_eq_two`.

## Lean progress — the ramification index travels, and the last statement is now fully scoped

```text
HTGeometry/RamificationIdxTransport.lean          (wired, built, axiom-clean)
    Ideal.map_le_map_iff_ringEquiv
    ramificationIdx'_algEquiv      ** e(ψ P / p) = e(P / p) along an algebra equivalence **
```

mathlib has only `Ideal.ramificationIdx_smul`, for a group acting on one fixed ring; two sheets of a
cover generate *different* subfields, so their places live on different integral closures and the
comparison needs an equivalence, not an action.  The proof is immediate on the `sSup` definition of
`ramificationIdx'` — `algebraMap R S₂ = ψ ∘ algebraMap R S₁`, so the two exponent sets coincide.
(On the `Module.length` definition it would need a localization comparison instead;
`ramificationIdx'_eq_ramificationIdx` converts afterwards.)

### The last statement, `∀ σ, e(Q_σ / 𝔪_A) ≤ 2`, scoped to the end

Sheets outside the collision support are already known unramified, so only colliding sheets remain,
and for those the chain is now completely identified:

```text
(1) the low coefficients of every sheet lie in W       criticalGeometricSheetToSchurFieldFibre_coefficients_mem
(2) their residues ARE the reduced fibre label          criticalGeometricSheetToSchurReducedFibre
(3) the SCALE is a unit of W, and its residue is fixed by (2):
        the fibre equation gives A.coeff 0 * B.coeff 0 = 1 over ANY commutative ring
        (TruncatedCompatibilityFibre, "the jet is invertible at the origin"), so applying it to the
        REDUCED fibre point makes the residue of the scale a unit
(4) hence the Schur coordinates — the raw coefficients normalised by the scale, and the reversed
        reciprocal squares — lie in W with residues fixed by the reduced label
(5) the Schur coordinates are algebraically independent, so the Schur coordinate ring is a
        POLYNOMIAL ring and its height-one localization is a DVR
        (algebraicIndependent_criticalSourceSchurCoordinates,
         criticalSchurCoordinateValuationSubring_isDiscreteValuationRing)
(6) two colliding sheets therefore have the same centre there, and
        ValuationSubring.eq_of_le_of_ne_top gives σ⁻¹(W) = criticalSchurSourceValuationSubring
        (which is criticalNormalClosureSchurValuationSubring_comap_source for the canonical sheet)
(7) criticalSchur_source_ramificationIdx_eq_two, moved along σ by ramificationIdx'_algEquiv
```

Step `(3)` is the find of this pass: the corpus already proves the constant terms of the jet and its
reciprocal are inverse to each other *over an arbitrary commutative ring*, so the statement holds
verbatim in the residue field, and no new integrality argument is needed to make the normalisation
legitimate.  That was the step that looked like it needed the coordinates to be integral over the
observation DVR, which they are not.

## Lean progress — step (3) of the last chain is DONE: the scale is a unit at every sheet

```text
HTGeometry/CriticalSheetJetUnit.lean              (wired, built, axiom-clean)
    criticalLowProduct_coeff_zero_mul     A.coeff 0 * B.coeff 0 = 1, over ANY commutative ring
    isUnit_criticalLowProduct_coeff_zero  hence the constant term is a UNIT
    isUnit_criticalSheetJetCoeffZero      for every sheet, in the upper Schur valuation ring

HTGeometry/CriticalSheetScaleUnit.lean            (wired, built, axiom-clean)
    coe_criticalSheetJetCoeffZero   the jet's zeroth coefficient IS the sheet's value on the scale
    criticalSheetScale_mem
    isUnit_criticalSheetScale       ** σ(scale) is a UNIT of W, for every geometric sheet σ **
```

The corpus's `coeff_zero_add_ne_zero_of_dvd` states this over a *field* and concludes only `≠ 0`.
The identity behind it — `A(0)·B(0) = 1` — needs no field at all, so it holds in the valuation ring
where the sheet's fibre point actually lives, and gives a **unit** rather than a nonzero element.
That is the difference that matters: the Schur normalisation divides by the scale, and the division
has to stay inside `W` for every sheet, not merely be defined in the fraction field.

This was the step that looked as if it needed the Schur coordinates to be integral over the
observation DVR — which they are not, and which no amount of work would have supplied.

**Remaining for `∀ σ, e(Q_σ/𝔪_A) ≤ 2`:** steps `(4)`–`(7)` of the chain above — extend
`isUnit_criticalSheetScale` from the scale to all the normalised Schur coordinates, read their
residues off the reduced fibre label, identify the centre on the (polynomial) Schur coordinate ring,
and transport `criticalSchur_source_ramificationIdx_eq_two` with `ramificationIdx'_algEquiv`.

## Lean progress — step (4): the Schur coordinates stay inside the valuation ring

```text
HTGeometry/SubringPolynomialCoefficients.lean     (wired, built, axiom-clean)
    PolyCoeffsIn  (+ .one .add .neg .sub .mul .pow .sum)
    finiteUnitPolynomial_polyCoeffsIn
    truncatedReciprocalKernel_polyCoeffsIn
    finiteReciprocalPositive_mem, finiteUnitSquarePositive_mem
    finiteReciprocalSquarePositive_mem
        ** the Schur coordinates of a family lying in a subring lie in that subring **
```

The corpus carries `PolynomialCoefficientsIn` for an `IntermediateField` — that is what the
*algebraic* statements about the Schur coordinates use.  The *arithmetic* statement needs the same
closure over a `Subring`, because a valuation subring is not a field.

What makes it work is that `truncatedReciprocalKernel N U = ∑_{j<N} (−(U−1))^j` involves **no
division**: the reciprocal coordinates are integral polynomial expressions in the normalised jet.
So once the scale is a unit of the valuation ring — which is `isUnit_criticalSheetScale`, proved
from the fibre equation alone — every Schur coordinate of every sheet lands in the pullback of that
valuation ring along the sheet, which is a subring of the source field.

Steps `(3)` and `(4)` of the chain are now both closed.  What is left of
`∀ σ, e(Q_σ/𝔪_A) ≤ 2` is `(6)`: two sheets with the same reduced fibre label have the same centre on
the Schur coordinate ring, and `ValuationSubring.eq_of_le_of_ne_top` identifies their pullbacks with
`criticalSchurSourceValuationSubring`; then `(7)` transports
`criticalSchur_source_ramificationIdx_eq_two` by `ramificationIdx'_algEquiv`.

## Lean progress — steps (a) and (b): every Schur coordinate of every sheet is integral

```text
HTGeometry/CriticalSheetSchurCoordinateIntegrality.lean   (wired, built, axiom-clean)
    criticalSourceRaw_of_le          a raw coordinate above the depth is an observation coordinate
    criticalSheetRaw_mem             ** every raw coordinate of every sheet lands in W **
    criticalSheetPullbackSubring     the pullback of W along a sheet, a subring of the source field
    criticalSourceNormalizedPositive_mem_pullback
    criticalSourceSchurCoordinates_mem_pullback
                                     ** and so does every Schur coordinate **
```

The corpus proves the Schur coordinates lie in the *source* Schur valuation subring, i.e. at the
place of the canonical embedding.  A general sheet induces a *different* place on the source field,
and the collision argument needs integrality at that one.  The raw coordinates split cleanly: below
the depth they are the low coefficients of the sheet's fibre point
(`criticalGeometricSheetToSchurFieldFibre_coefficients_mem`); above it they are **observation**
coordinates, which a sheet fixes and which are integral at the observation Schur place
(`criticalObservationRaw_mem_observationValuationSubring`).  The passage to the Schur coordinates is
`finiteReciprocalSquarePositive_mem` together with `isUnit_criticalSheetScale`.

**Recorded no-go.**  `σ⁻¹(W) ⊇ criticalSchurSourceValuationSubring` is FALSE for a general sheet —
distinct sheets induce distinct places over the same base, which is exactly why only some sheets
collide.  Integrality of the coordinates is what is true; identifying the places needs the residues.

Steps `(3)`, `(4)`, `(a)`, `(b)` of the chain to `∀ σ, e(Q_σ/𝔪_A) ≤ 2` are closed.  What is left is
`(c)` two sheets with the same reduced fibre label have equal residues on all Schur coordinates,
hence the same centre; `(d)` the centre's localization is `criticalSchurSourceValuationSubring`, a
DVR, so `ValuationSubring.eq_of_le_of_ne_top` identifies the pullbacks; `(e)` transport
`criticalSchur_source_ramificationIdx_eq_two` by `ramificationIdx'_algEquiv`.

## Lean progress — the Schur coordinate construction is natural, so residues transport

```text
HTGeometry/RingSchurCoordinates.lean              (wired, built, axiom-clean)
    ringUnitPolynomial, ringTruncatedReciprocalKernel
    ringReciprocalPositive, ringUnitSquarePositive, ringReciprocalSquarePositive
    ringUnitPolynomial_eq, ringTruncatedReciprocalKernel_eq, ringReciprocalSquarePositive_eq
        the ring versions are DEFINITIONALLY the corpus's field versions
    ringUnitPolynomial_map, ringTruncatedReciprocalKernel_map,
    ringReciprocalPositive_map, ringUnitSquarePositive_map,
    ringReciprocalSquarePositive_map
        ** f (coordinate of u) = coordinate of (f ∘ u), for EVERY ring hom f **
```

No step of the Schur construction divides — the unit polynomial is `1 + ∑ u_i X^{i+1}`, the
truncated reciprocal kernel is `∑_{j<N} (−(U−1))^j`, the square is a square — so it lives over any
commutative ring, definitionally agrees with the corpus's field version, and is natural.

That naturality is exactly what step `(c)` needs, and it is inexpressible while the construction is
stated only over a field: the map it has to be applied to is the **residue map of the upper Schur
valuation ring**, a ring hom out of a ring that is not a field.  With it, two sheets whose fibre
coefficients have equal residues have equal residues on every Schur coordinate.

Remaining for `∀ σ, e(Q_σ/𝔪_A) ≤ 2`: assemble `(c)` from `ringReciprocalSquarePositive_map` applied
to the residue map plus `criticalGeometricSheetToSchurReducedFibre`; then `(d)` the centre's
localization is `criticalSchurSourceValuationSubring`, a DVR, so `ValuationSubring.eq_of_le_of_ne_top`
identifies the pullbacks; then `(e)` `ramificationIdx'_algEquiv`.

## Lean progress — `(R)` IS CLOSED: the Schur inertia group has order exactly two

`natCard_criticalSchurInertiaGroup_le_two_of_ramification` no longer carries a hypothesis.  Six
further modules landed, all `lake build`-green and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), all wired into `HTGeometry.lean`:

```text
HTGeometry/CriticalSheetResidueCongruence.lean
    coe_criticalSheetJetCoeff        the j-th jet coefficient IS the sheet's j-th raw coordinate
    criticalSheetToUpper, criticalSheetResidue
    criticalSheetRaw_residue_congr   ** equal labels ⟹ equal residues on every raw coordinate **
HTGeometry/CriticalSheetSchurCoordinateResidue.lean
    criticalSheetSchurCoordinates_residue_congr
                                     ** … hence on every Schur coordinate **
HTGeometry/CriticalSheetCoordRingResidue.lean
    coe_algebraMap_criticalSchurSourceValuationSubring
    criticalSheetAevalHom, criticalSheetCoordResidue
    criticalSheetCoordResidue_congr  ** … hence on the whole Schur coordinate ring **
HTGeometry/CriticalSheetSchurPlacePullback.lean
    criticalSheetPullbackValuation, criticalSheetPullbackValuation_canonical
    isUnit_criticalSheetAeval
    criticalSheetPullbackValuation_eq
        ** a sheet with the canonical label cuts out exactly the source Schur place **
HTGeometry/CriticalSheetPlaceRamificationIndex.lean
    criticalSheetFieldEquiv, criticalSheetIntegralClosureEquiv
    criticalSheetIntermediateCentre_comap
    criticalSheetRamificationIdx_eq_two   ** e(Q_σ) = 2 for such a sheet **
HTGeometry/CriticalSchurInertiaOrderTwo.lean
    criticalSourceNormalClosureEmbedding_mem_collisionSupport
    criticalSheetRamificationIdx_le_two   ** every sheet: e(Q_σ) ≤ 2 **
    natCard_criticalSchurInertiaGroup_le_two
    natCard_criticalSchurInertiaGroup_eq_two   ** |I| = 2 **
```

### The argument, and why it is not circular

`e(Q_σ)` is by the orbit formula the size of the `I`-orbit of `σ`, so bounding it looks equivalent
to the collision count.  It is not, because it is computed *arithmetically*, from the place the
sheet cuts out, and not from any orbit:

1. the reduced label of a sheet is the residue of its fibre point, so two sheets with the same label
   have the same residue on every raw coordinate — below the depth those residues are the label's
   own coefficients, above it the coordinate is an observation coordinate that every sheet fixes;
2. the scale is a unit of the upper valuation ring at every sheet (`isUnit_criticalSheetScale`), and
   the Schur coordinates are a division-free polynomial construction in the normalised raws
   (`RingSchurCoordinates`), so the residues agree on every Schur coordinate, hence — the coordinate
   ring being a polynomial ring — on the whole coordinate ring;
3. the source Schur valuation ring is the localization of that polynomial ring at the Schur prime,
   so its elements are ratios whose denominators lie outside the prime; those denominators have
   nonzero residue along the sheet, hence are invertible there, hence the sheet's pullback contains
   the source Schur valuation ring; being a proper valuation ring over a one-dimensional one, it
   equals it;
4. a sheet is an isomorphism onto its own field range, and carries the integral closure and its
   centre along, so `e(Q_σ)` is the ramification index of the *source Schur place*, already computed
   as `2` by `criticalSchur_source_ramificationIdx_eq_two`;
5. the canonical embedding cuts out the source Schur place, so it is ramified, so it lies in the
   collision support; every colliding sheet therefore shares its label; every non-colliding sheet is
   unramified.  Hence `∀ σ, e(Q_σ) ≤ 2`, and cyclicity of tame inertia gives `|I| ≤ 2`.

With `criticalSchur_two_le_ramificationIdxIn` (already unconditional) this pins `|I| = 2`.

### What `(D)` still needs

`|I| = 2` gives `e(w_std / p) = 2` and hence `t := e(w / w_std) = 1`: the normal-closure place is
unramified over the source Schur place.  The reduction-degree bound `hdeg` of
`criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_reducedFibre_degree` still needs the *fibre
count*: at most two sheets carry the canonical label.  Two routes, both now short of one step:

```text
(A)  the derivative count.  Choose θ integral over the observation Schur DVR A with E(θ) = F_src;
     every sheet sends it into W (a valuation ring is integrally closed), the minimal polynomial is
     monic over A and splits in L, and RootCongruenceValuationCount.
     card_congruent_roots_le_addVal_eval_derivative bounds the label fibre by 1 + w(p'(θ_σ)).
     With t = 1 that is 1 + v_{w_std}(p'(θ)), and the missing step is exactly LOCAL MONOGENICITY —
     V = A_p[θ] — which turns v(p'(θ)) into the different exponent, equal to e − 1 = 1 in the tame
     case (DifferentIdealMonogenic + DifferentExponentTame.differentIdeal_eq_span_pow).
(B)  the residue degree.  The label fibre is the set of sheets over the source Schur place with one
     fixed residue, of size e·f/f = e = 2 as soon as f(w_std / p) = 1, which is §3's birationality
     of the ramification divisor onto the branch divisor
     (criticalFibre_eq_of_shared_coprime_tangent, already Lean).  The missing step is the counting
     identity "#sheets over a place = e·f".
```

### Correction — the exact remaining statement of `(D)`, after `(R)`

Chasing the two routes above to the end shows they are the same statement, and identifies it
exactly.  With `|I| = 2` in hand:

* every sheet whose place is the source Schur place has `e(Q_σ) = 2`
  (`criticalSheetRamificationIdx_eq_two`, whose hypothesis is the *place*, not the label), hence a
  free inertia orbit, hence collides;
* conversely a colliding sheet shares the canonical label (`criticalSchur_collisionSupport_reducedFibre_eq`)
  and therefore cuts out the source Schur place (`criticalSheetPullbackValuation_eq`).

So the collision support is exactly the set of sheets over the source Schur place, and it is a
single fibre of the reduced label.  Its size is `e·f = 2·f(w_std / p)`.  Hence

```text
(D)   ⟺   f(w_std / p) = 1   ⟺   the label fibre of a sheet is a single inertia orbit.
```

`(A)` above also reduces to this: the corpus's tame-different theorems
(`DifferentExponentTame.differentIdeal_eq_span_pow`,
`TameDifferentMonogenic.addVal_eval_derivative_of_monic_uniformizer_root`) all assume a *trivial
residue extension*, i.e. exactly `f = 1`; and a uniformizer of the source place satisfies an
Eisenstein relation of degree `e` over the base only in the totally ramified case.

Geometrically `f = 1` is §3: the ramification divisor maps birationally onto the branch divisor.
The Lean route does not go through coordinates, but through the decomposition dictionary at the
level of valuation subrings — two general theorems, neither in mathlib, both worth having:

```text
(i)   transitivity: for L/F Galois and two valuation subrings of L with the same restriction to an
      intermediate field M, some element of Gal(L/M) carries one to the other.
      Mathlib has the ideal-theoretic form, Ideal.exists_smul_eq_of_isGaloisGroup; the bridge is
      ValuationSubringInertiaDictionary.valuationSubringAtPrime_eq.
(ii)  |D_W over M| = |I_W over M| · f, together with Nat.card (Aut (k_W / k_w)) ≤ f.
      Mathlib has Ideal.card_stabilizer_eq_card_inertia_mul_finrank; the same bridge transports it.
```

Given (i) and (ii): a sheet `τ` with the canonical label cuts out `w_std`, so `τ = g ∘ σ₀` for some
`g ∈ Gal(L/E)` (normality), which (i) lets us take in the decomposition group; its residue fixes
`k_{w_std}` because the labels agree, and since `|I_{W/σ₀F}| = e(W/w_std) = t = 1` the map
`D_{W/σ₀F} → Aut(k_W / k_{w_std})` is injective between sets of the same size `f(W/w_std)`, hence
surjective, so `g` can be corrected by an element of `Gal(L/σ₀F)` into the inertia group.  Then the
label fibre is the inertia orbit of `σ₀`, of size `|I| = 2`, which is `(D)` and hence `hdeg`.

## The two named missing general theorems now exist (2026-08-23)

The previous entry identified `(D)` as needing two theorems "neither in mathlib, both worth having".
Both are now in the tree, axiom-clean and umbrella-wired, in
`formal/GaloisForLFunctions/HTGeometry/ValuationSubringDecompositionOrder.lean`:

```text
ValuationInertia.exists_smul_valuationSubring_eq
    (p : Ideal R) [p.IsMaximal] (W₁ W₂ : ValuationSubring L) (hW₁ hW₂ : · ≠ ⊤)
    (hRW₁ hRW₂) (hcent₁ hcent₂ : the nonunits of Wᵢ meet R exactly in p) :
  ∃ g : L ≃ₐ[F] L, g • W₁ = W₂                                              -- (i)

ValuationInertia.natCard_decompositionSubgroup_eq_natCard_inertiaSubgroup_mul_inertiaDegIn
    (p : Ideal R) [p.IsMaximal] [PerfectField p.ResidueField] (W) (hW) (hRW) (hcent) :
  Nat.card (W.decompositionSubgroup F)
    = Nat.card (W.inertiaSubgroup F) * Ideal.inertiaDegIn p T                -- (ii)
```

with the hinge

```text
ValuationInertia.smul_valuationSubring_eq_iff_smul_centerPrime_eq
  g • W = W  ↔  g • centerPrime W = centerPrime W
```

— the decomposition subgroup of a valuation subring *is* the stabiliser of its centre, so mathlib's
`Ideal.exists_smul_eq_of_isGaloisGroup` and `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`
transport verbatim through `ValuationSubringInertiaDictionary` /
`ValuationSubringGaloisTransport`.  The base field `F` is arbitrary among those over which `L` is
Galois, so both hold at every intermediate field of the tower, which is what the sheet count needs.

The only new argument is the stabiliser identity: a Galois element carrying `W` to itself carries
its nonunits to its nonunits, because an inverse produced inside `W` after transport comes back
inside `W`.

**What `(D)` still needs.** With (i) and (ii) in hand the card's own chase goes through: a sheet `τ`
with the canonical label cuts out `w_std`, (i) puts the correcting element in the decomposition
group, and (ii) plus `|I_{W/σ₀F}| = 1` makes `D → Aut(k_W/k_{w_std})` injective between sets of size
`f(W/w_std)`, hence surjective — so the label fibre is the inertia orbit of `σ₀`, of size `|I| = 2`.
The remaining input is `f(w_std / p) = 1`, i.e. §3's birationality of the ramification divisor onto
the branch divisor, in the form the `criticalSchur` place data can consume.

## `f = 1`: the algebraic heart is now in the tree (2026-08-23)

The remaining input for `(D)` is `f(w_std/p) = 1` — "the ramification divisor maps birationally onto
the branch divisor".  Its algebraic content is that the Schur ramification polynomial is **linear in
its marked ramification coordinate**, and that fact is *already* a corpus theorem:

```text
degreeOf_ramificationCoordinate_criticalSourceSchurRamificationPolynomial
    (hm : 1 < m) (hn : 1 < n) :
  MvPolynomial.degreeOf (criticalSchurRamificationCoordinateIndex _ _)
    (criticalSourceSchurRamificationPolynomial K m n) = 1
```

(`HTGeometry/CriticalSchurMarkedUnits.lean`).

What that degree-one fact *buys* is now general and proved, in
`formal/GaloisForLFunctions/HTGeometry/LinearDivisorResidueField.lean` (axiom-clean, wired):

```text
ker_aeval_linearRoot (F) [IsFractionRing S F] {a b : S} (ha : a ≠ 0)
    (hprim : (C a * X + C b).IsPrimitive) :
  RingHom.ker (aeval (linearRoot F a b) : S[X] →ₐ[S] F) = Ideal.span {C a * X + C b}

injective_quotient_lift_aeval_linearRoot :
  the residue ring S[X] ⧸ (C a * X + C b) embeds in F
```

Gauss's lemma (`Polynomial.IsPrimitive.dvd_iff_fraction_map_dvd_fraction_map`) turns divisibility in
`F[X]` into divisibility in `S[X]`, so the kernel is exactly the principal ideal, and the residue
ring of the divisor sits inside `Frac S` — which `S` already generates.  That is residue degree one.

### What is left for `(D)`

Only the card-specific bookkeeping: split `criticalSchurSourceRing K m n = MvPolynomial (Fin (m+n)) K`
as `S[X]` with `X` the marked ramification coordinate and `S` the polynomial ring in the remaining
coordinates (`MvPolynomial.optionEquivLeft` along `Equiv.optionSubtypeNe`), read the degree-one fact
as `g = C a * X + C b`, note that `g` is primitive because it is irreducible of positive degree
(`irreducible_criticalSourceSchurRamificationPolynomial`), and identify `Frac S` with the residue
field of the restricted place on the observation field.  Then `f = 1`, the label fibre is the inertia
orbit of size `|I| = 2`, and `hdeg` follows through
`exists_criticalGeometricMonodromy_isSwap_of_reducedFibre_degree`.

## `f = 1` IS NOT NEEDED — the residue degree cancels (2026-08-23)

The previous entries reduced `(D)` to `f(w_std / p) = 1`, following the card's own chase: the label
fibre of a sheet was to be identified with the inertia orbit by making `D_{W/σ₀F} → Aut(k_W/k_{w_std})`
*injective between sets of the same size*, which needs `|I_{W/σ₀F}| = 1` and therefore
`e(w_std/p) = e(W/p)`, and then the fibre size `e·f = 2f` forces `f = 1`.

**That detour is unnecessary, and `f` never has to be computed.**  Write `M := σ(E)` for the
intermediate field a sheet generates, `Q_M` for the centre of `W` on the integral closure of the
observation Schur DVR in `M`.  A sheet `τ` with the same reduced label as `σ`

* cuts out the same place, so `τ = g ∘ σ` with `g` in the decomposition group of `W` over `F`
  (normality of `L/F`, then `exists_smul_valuationSubring_eq` over `M` to move `g` into `D_W(F)`);
* has the same residue map, so the induced `ḡ` fixes the residue field of `Q_M` pointwise.

Now correct `g` *inside* `Gal(L/M)`: because the decomposition group of `W` over `M` realises
**every** automorphism of `k_W` over `k_{Q_M}`, there is `h ∈ D_W(M)` with `h̄ = ḡ`, and
`i := g h^{-1}` lies in inertia while `i|_M = g|_M` — so `τ = i ∘ σ`.  The label fibre is inside one
inertia orbit and has at most `|I| = 2` elements.  The residue degree `f(W/w_std)` appears on both
sides of the correction and cancels; nothing about `f(w_std/p)` is used.

The surjectivity is mathlib's `Ideal.Quotient.stabilizerHom_surjective` — no counting, no
`PerfectField` hypothesis, no `|I_{W/M}| = 1`.

**The general theorem is now in the tree**, axiom-clean and umbrella-wired, in
`formal/GaloisForLFunctions/HTGeometry/ValuationInertiaIntermediateResidueLift.lean`:

```text
ValuationInertia.exists_mem_inertia_eq_on_intermediateField
    (M : IntermediateField F L) (W : ValuationSubring L) (hAW) (hW : W ≠ ⊤)
    (hgW : g • W = W)
    (hres : ∀ b : integralClosure A M, g • algebraMap b - algebraMap b ∈ centerPrime W) :
  ∃ i : L ≃ₐ[F] L, i ∈ (centerPrime W).inertia (L ≃ₐ[F] L) ∧ ∀ x : M, g x = i x

ValuationInertia.exists_mem_inertiaSubgroup_eq_on_intermediateField
  the same with `i` produced inside `W.inertiaSubgroup F`
```

with the supporting instances `smulCommClass_intermediate`
(`SMulCommClass Gal(L/M) (integralClosure A M) (integralClosure A L)`),
`comap_centerPrime_eq_intermediateCentre` and `liesOverCentre`
(`(centerPrime W).LiesOver (intermediateCentre M W)`), which is what lets mathlib's ideal-theoretic
Hilbert theory run at an intermediate field of a *non-normal* step.

### What `(D)` needs now

Only the horizon-side instantiation, in three pieces:

```text
(a)  same label ⟹ same place                      criticalSheetPullbackValuation_eq   (Lean)
(b)  same label ⟹ same residue on the integral closure of the observation Schur DVR in σ(E).
     criticalSheetSchurCoordinates_residue_congr already gives it on the Schur coordinates,
     and the Schur coordinate ring generates that integral closure up to the centre, because
     the source Schur valuation ring IS the localization of the Schur coordinate ring at the
     ramification prime (criticalSchurCoordinateValuationSubring, valuationSubringAtPrime_eq).
(c)  τ = g ∘ σ with g ∈ D_W(F):  normality of L/F gives g ∈ Gal(L/F); (a) plus
     exists_smul_valuationSubring_eq over σ(E) moves it into the decomposition group.
```

Then `exists_mem_inertia_eq_on_intermediateField` gives `τ = i ∘ σ` with `i` in inertia, the label
fibre has at most `Nat.card (criticalSchurInertiaGroup) = 2` elements, and
`criticalSchur_collisionSupport_ncard_le_two_of_fibre` closes `(D)`.

## `(D)` IS CLOSED — the monodromy contains a transposition, unconditionally (2026-08-23)

The bypass of the previous entry is now carried out in full.  Five modules, all axiom-clean and
umbrella-wired:

```text
HTGeometry/ValuationInertiaIntermediateResidueLift.lean
    smulCommClass_intermediate, comap_centerPrime_eq_intermediateCentre, liesOverCentre
    exists_mem_inertia_eq_on_intermediateField
        ** g stabilises W and fixes the residues of the intermediate base
             ⟹ g agrees on M with an inertia element **
    exists_mem_inertiaSubgroup_eq_on_intermediateField

HTGeometry/ValuationInertiaSheetInertiaOrbit.lean
    isUnit_valuationSubring_iff, isUnit_congr, comap_eq_inv_smul, comapRingEquiv,
    isUnit_comap_iff, comap_ne_top, restrictScalars_smul_valuationSubring
    exists_algEquiv_comp_eq        two embeddings into a Galois extension differ by a Galois element
    exists_mem_inertia_comp_eq
        ** σ, τ : E →ₐ[F] L with the same place and the same residue map ⟹ τ = i ∘ σ, i ∈ inertia **
    exists_mem_inertiaSubgroup_comp_eq

HTGeometry/CriticalSheetLabelInertiaOrbit.lean
    criticalSheet_residue_eq_of_canonical_label
        ** equal canonical labels ⟹ equal residues at EVERY element of the source Schur place **
    criticalSchur_exists_inertiaSubgroup_comp_eq

HTGeometry/CriticalSchurCollisionSupportBound.lean
    Set.ncard_range_le_natCard
    criticalSchur_collisionSupport_ncard_le_two      ** `(D)` **
    exists_criticalGeometricMonodromy_isSwap        ** `(3)`, UNCONDITIONAL **
    criticalGeometricMonodromy_eq_top_of_isPreprimitive
```

The residue statement is lifted from the Schur coordinates to the whole place by
`IsLocalization.surj` on the source Schur valuation ring: an element is `aeval a / aeval b` with `b`
off the Schur prime, the two labels give `coordResidue σ = coordResidue τ`, and
`isUnit_criticalSheetAeval` makes the denominator's residue invertible.

`exists_criticalGeometricMonodromy_isSwap` needs no hypotheses at all: `natCard_criticalSchurInertiaGroup_eq_two`
supplies the nontriviality and `criticalSchur_collisionSupport_ncard_le_two` the collision count.

### Elaboration notes, so no session re-derives them

* The subtype `⟨i, hi⟩ : criticalSchurInertiaGroup K hm hn` from a proof `hi` of membership in
  `(criticalNormalClosureSchurValuationSubring …).inertiaSubgroup …` is a **defeq check the unifier
  cannot afford** in a context carrying the horizon's field tower — it exhausts 8M heartbeats.
  Working with `.inertiaSubgroup` directly costs nothing.  `Nat.card` of the two is interchangeable
  cheaply, so `natCard_criticalSchurInertiaGroup_le_two` applies verbatim to the subgroup form.
* A hypothesis term passed inline to a lemma with several implicit arguments (here the residue
  congruence) blows up; binding it first with `have hres0 := …` and passing the local name does not.

### What the card still needs

Only `(4)`'s **primitivity**, i.e. §4: the monodromy action on sheets is preprimitive.  The corpus
has the conditional form `criticalMonodromy_isPreprimitive_of_rootAction_le`
(`HTGeometry/OccupationSubsetPrimitivity.lean`) — any monodromy subgroup containing the full
unbalanced root-permutation action is primitive — together with
`criticalOccupationRootAction_isPreprimitive`.  Everything else on the card is Lean-closed.

## Primitivity: the E-chain after `(D)`, and its group-theoretic core (2026-08-23)

With `(D)` closed, the card's remaining obligation is `(iii)` primitivity, which the 2026-08-18
programme resolves into `E1`–`E7`.  Current state:

```text
E1  branch locus in the chart = the Schur divisor     DONE  UnramifiedAwayFromDerivative
                                                            isUnramifiedAt_of_aeval_derivative_notMem
E2  the Schur meridian is one transposition           DONE  this session — exists_criticalGeometricMonodromy_isSwap
E3  the block field is unramified at every height-one prime of the chart
        group-theoretic half                          DONE  this session — see below
        Galois-correspondence half                    OPEN  (block ↔ intermediate field of L/F)
E4  T-equivariance to the slice                       OPEN  (bookkeeping)
E5  SCE_k                                             DONE  rank_eq_one_of_isUnit_discr_mvPolynomial
E6  M ⊆ O(c^{1/L}) cyclic and v_m(c) = 1 ⟹ M = O      OPEN  (one valuation)
E7  trivial block system ⟹ primitive                  DONE  this session — see below
```

The group-theoretic core of `E3` and `E7` is now a general theorem, axiom-clean and umbrella-wired,
in `formal/GaloisForLFunctions/HTGeometry/TranspositionBlockInvariance.lean`:

```text
isBlock_smul_eq_of_swapLike, isBlock_smul_eq_of_isSwap, isBlock_smul_eq_of_eq_one_or_isSwap
    ** an element acting as a transposition preserves every block with two or more elements **
exists_block_of_not_isPreprimitive
```

The proof is the right one: a block is preserved or moved off itself, and moving it off itself would
require moving *every* one of its points, which a transposition cannot do to a set of size ≥ 2
unless that set is the transposed pair — which it preserves.  So the inertia generated by the Schur
meridian lies in the stabiliser of every block, which is exactly what makes the block field
unramified at the Schur place.

**Elaboration warning.**  Instantiating this on the horizon —
`criticalSchurInertiaAction_eq_one_or_isSwap_of_collisionSupport_ncard_le_two` fed into
`isBlock_smul_eq_of_eq_one_or_isSwap` — runs into the same wall recorded above: building the
`criticalGeometricMonodromy` subtype from `criticalSchurInertiaAction_range_le_monodromy` did not
finish in ten minutes.  Route it through a statement quantified over a *given*
`t : criticalGeometricMonodromy K m n` with `(t : Equiv.Perm _) = 1 ∨ (t : Equiv.Perm _).IsSwap`,
which is what `isBlock_smul_eq_of_eq_one_or_isSwap` already takes.

## `E3`'s ramification half is now a general theorem (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/ValuationInertiaIntermediateUnramified.lean`, axiom-clean and
umbrella-wired:

```text
ValuationInertia.toIntermediateAlgEquiv          an F-automorphism fixing M is an M-automorphism
ValuationInertia.smul_valuationSubring_intermediate
ValuationInertia.mem_inertiaSubgroup_intermediate
    ** inertia membership does not depend on the base field **
ValuationInertia.natCard_inertiaSubgroup_le_intermediate
ValuationInertia.ramificationIdx_intermediateCentre_eq_one_of_inertia_fixes
    ** if inertia fixes M pointwise then e(Q_M / p) = 1 **
```

The proof is the orbit formula run backwards: `natCard_inertiaSubgroup_eq_intermediate_mul` gives
`|I_F| = e · |I_M|`, and if every inertia element fixes `M` pointwise then `I_F` injects into `I_M`,
so `e · |I_M| ≤ |I_M|` with `|I_M| > 0`, i.e. `e = 1`.  Nothing assumes `M/F` normal.

Together with `TranspositionBlockInvariance` this is the whole of `E3`: the Schur meridian acts as a
transposition (`exists_criticalGeometricMonodromy_isSwap`), a transposition preserves every block
with two or more elements, so the inertia fixes the block field, so the block field is unramified at
the Schur place; and `isUnramifiedAt_of_aeval_derivative_notMem` (`E1`) handles every other
height-one prime of the chart.

Remaining for the card: the Galois-correspondence bookkeeping "block ↦ intermediate field" on the
horizon's own sheet action, `E4` (T-equivariance to the slice) and `E6` (the Kummer valuation).
`E5` is `rank_eq_one_of_isUnit_discr_mvPolynomial`.

## `E3` in block form and `E6`'s core (2026-08-23)

Two more general theorems, axiom-clean and umbrella-wired.

```text
HTGeometry/ValuationInertiaIntermediateUnramified.lean
    ValuationInertia.ramificationIdx_fixedField_eq_one_of_inertia_le
        ** the field fixed by ANY subgroup containing inertia is unramified at the place **

HTGeometry/KummerRootValuationOrder.lean
    eq_one_of_pow_eq_of_addVal_eq_one            (discrete valuation ring)
    eq_one_of_pow_eq_of_addValuation_eq_one      (integer-valued valuation on a field)
        ** z^k = c with v(c) = 1  ⟹  k = 1 **
```

The first is `E3` in exactly the form a block system consumes: take `H` to be the stabiliser of a
block, which contains the inertia because a meridian transposition preserves every block of size ≥ 2
(`TranspositionBlockInvariance`).  The second is `E6`'s only mathematical content — an intermediate
field of the cyclic `O(c^{1/L})/O` is `O(c^{1/k})` with `k ∣ L`, and the marked coordinate divisor
gives `v_m(c) = 1`, so `k = 1`.

**Card status.**  `E1`, `E2`, `E3`, `E5`, `E7` are Lean-closed, and `E6`'s valuation step is closed.
Open: (a) `E4`, the torus/slice equivariance moving unramifiedness from the chart to
`K[w₁,…,w_{L-2}]`; (b) the Kummer-theoretic half of `E6`, that an intermediate field of the cyclic
`O'/O` has the form `O(c^{1/k})`; (c) the horizon bookkeeping that assembles them.  Everything else
on the card is Lean-closed.

## `E6`'s structural half is now a general theorem (2026-08-23)

Appended to `HTGeometry/ValuationInertiaIntermediateUnramified.lean`, axiom-clean and wired:

```text
ValuationInertia.intermediateField_eq_bot_of_unramified_of_totallyRamified
    ** a totally ramified place has no unramified subextension **
ValuationInertia.fixedField_eq_bot_of_inertia_le_of_totallyRamified
    ** at a totally ramified place, a subgroup containing inertia has trivial fixed field **
```

The proof is the orbit formula plus a degree count: `|I_F| = e(Q_M/p)·|I_M| = |I_M|` when `M` is
unramified, `I_M` embeds in `Gal(L/M)` so `|I_M| ≤ [L:M]`, and total ramification gives
`[L:F] ≤ |I_F|`; hence `[M:F]·[L:M] ≤ [L:M]`, so `[M:F] = 1`.

This is exactly `E6` in structural form.  The cyclic extension `O' = O(c^{1/L})` is **totally
ramified** at the marked divisor where `v_m(c) = 1` — `w(z) = 1` and `w(c) = L` — so any block field
inside it that is unramified there is trivial.  No Kummer classification of subextensions is needed:
the degree count does the work, and `KummerRootValuationOrder` supplies the valuation computation
that makes the place totally ramified.

**What `E6` still needs**: the statement `Module.finrank O O' ≤ Nat.card (W.inertiaSubgroup O)` for
the horizon's `O' = O(c^{1/L})` — i.e. `e ≥ L` at the marked divisor, from `w(z) ≥ 1` and
`w(z^L) = w(c) = e·v_m(c) = e`.  Together with `E4` (the torus/slice equivariance) and the horizon
bookkeeping, that is all that is left of `(4)`, and therefore of this card and of
`projective-horizon-one-step-postcritical-rigidity`, which is reduced to `(4)` alone.

## The total-ramification criterion (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/RamificationIndexLowerBound.lean`, axiom-clean and wired —
a mathlib gap:

```text
le_ramificationIdx'_of_map_le_pow          map p ≤ P^k  ⟹  k ≤ ramificationIdx' p P
le_ramificationIdx'_of_map_le_span_pow     map p ≤ (z^k) with z ∈ P  ⟹  k ≤ ramificationIdx' p P
```

mathlib carries only the upper half of `ramificationIdx'`'s defining property
(`le_pow_of_le_ramificationIdx'`); the lower half is the factorisation count over a Dedekind domain,
which is what an Eisenstein-type root needs.

This is the missing inequality for `E6`: the marked divisor of `O' = O(c^{1/L})` has `c = z^L` with
`z` in the prime above, so `e ≥ L = [O':O]`, i.e. the place is **totally ramified**, and
`ValuationInertia.fixedField_eq_bot_of_inertia_le_of_totallyRamified` then kills the block field.

`E6` is therefore complete as a chain of general theorems.  What remains of `(4)` is `E4` — the
torus/slice equivariance that moves the everywhere-unramifiedness from the chart to the slice ring
`K[w₁,…,w_{L-2}]`, where `E5` (`rank_eq_one_of_isUnit_discr_mvPolynomial`) applies — and the horizon
bookkeeping that instantiates the chain.  The corpus already owns the torus-chart objects
(`LocalizationTwoPrimeUnits.TorusChart`, `TorusChartFundamentalGroup`,
`CriticalObservationChartRing`), so `E4` is assembly on existing types rather than new mathematics.

## `(4)`: the complete assembly, with every general theorem now in the tree (2026-08-23)

Every step of the endgame is a Lean theorem; what is left is horizon instantiation.  The chain, in
the order a session should build it:

```text
1.  a nontrivial block B of the monodromy action on sheets
        exists_block_of_not_isPreprimitive                  (TranspositionBlockInvariance)  DONE
    ⟹ the block field M := fixedField (stabilizer B),  F ⊊ M ⊆ σ₀(E)

2.  M/O is unramified at EVERY height-one prime of the chart ring
      • at the Schur prime: the meridian is a transposition (exists_criticalGeometricMonodromy_isSwap,
        DONE) and a transposition preserves every block of size ≥ 2
        (isBlock_smul_eq_of_eq_one_or_isSwap, DONE), so inertia ⊆ stabilizer B, and
        ValuationInertia.ramificationIdx_fixedField_eq_one_of_inertia_le (DONE) gives e = 1;
      • elsewhere: isUnramifiedAt_of_aeval_derivative_notMem  (E1, already in the tree)
    ** needs: the horizon instantiation of these two, on criticalObservationChartRing **

3.  the torus slice.  T = 𝔾ₘ² acts, S = {x_m = 1, y_n = 1} ≅ 𝔸^{L-2}, c = x_m y_n,
    O' = O(c^{1/L}) = O_S(λ, μ) purely transcendental of degree 2 over the slice field.
      • freeParameterBaseChange / freeParameterPermEquiv   (FreeParameterBaseChange)  ALREADY IN TREE
      • rank_eq_one_of_isUnit_discr_mvPolynomial            (SCE_k)                   ALREADY IN TREE
    ⟹ M_S = O_S, hence M ⊆ O'
    ** needs: the slice presentation of O' on the horizon's own fields **

4.  the marked divisor is TOTALLY RAMIFIED in O':  c = z^L with z in the prime above, so
        le_ramificationIdx'_of_map_le_span_pow             (RamificationIndexLowerBound)  DONE
    and step 2 says M is unramified there, so
        ValuationInertia.fixedField_eq_bot_of_inertia_le_of_totallyRamified            DONE
    gives M = ⊥ — contradicting F ⊊ M.

5.  hence no nontrivial block: the action is preprimitive, and
        criticalGeometricMonodromy_eq_top_of_isPreprimitive (DONE, this session)
    is `(4)`.
```

Note that step 4 makes the Kummer-relation endpoint (`criticalSource_not_exists_kummer_relation`,
`dvd_exponents_of_eq_pow_torusChart`) **unnecessary**: step 3 only has to deliver `M ⊆ O'`, and the
total-ramification count finishes.  Those modules remain as an independent second route.

So the two open items are both instantiation: `(2)` on the chart ring and `(3)`'s slice presentation.
No general mathematics is missing.  `projective-horizon-one-step-postcritical-rigidity` is reduced to
this same `(4)` and needs nothing of its own.

## Step 2's Schur half is INSTANTIATED on the horizon (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/CriticalBlockFieldUnramified.lean`, axiom-clean, wired:

```text
criticalBlockStabilizer B                     the stabiliser of a block inside Gal(L/F)
criticalSchurInertia_smul_block_eq            inertia preserves every block of size ≥ 2
criticalSchurInertia_le_blockStabilizer
criticalSchurInertia_ramificationIdx_blockField_eq_one
    ** e(Q_M / p) = 1 for M = fixedField (criticalBlockStabilizer B) **
```

The elaboration wall recorded earlier is **avoidable**: it came from *constructing* the subtype
`⟨t, htG⟩` of a horizon-sized subgroup.  Restating the general lemma to take the permutation together
with a membership proof (`isBlock_perm_smul_eq_of_eq_one_or_isSwap`) moves that construction into a
context where the group is a variable, and the horizon instantiation then takes **ten seconds**.  The
converse direction — using an element of `W.inertiaSubgroup F` where `criticalSchurInertiaGroup` is
expected — was always free; only the construction was expensive.

Remaining for `(4)`: step 2's non-Schur half (`isUnramifiedAt_of_aeval_derivative_notMem` on the
chart ring) and step 3's slice presentation.

## The unramified-to-unit-discriminant glue (2026-08-23)

Added to `HTGeometry/RamificationIndexLowerBound.lean`, axiom-clean:

```text
isUnit_of_forall_notMem_isPrime
    ** over a UFD, a nonzero element in no nonzero prime is a unit **
```

`SCE_k` (`rank_eq_one_of_isUnit_discr_mvPolynomial`) consumes `IsUnit (Algebra.discr R e)`, a global
condition; step 2 delivers unramifiedness prime by prime.  This is the bridge: over the slice
polynomial ring, a discriminant lying in no height-one prime is a unit.

The remaining link on that side is `differentIdeal = 1 ⟹ IsUnit disc`, for which the tree already
owns the monogenic case (`DifferentIdealMonogenic.differentIdeal_eq_span_aeval_derivative`: with
trivial conductor the different is generated by `p'(x)`), and `Algebra.discr_powerBasis_eq_norm`
converts `p'(x)` to the discriminant.  Recorded so the next session does not re-derive the route.

## Step 2 is COMPLETE in general form (2026-08-23)

The second half is now a theorem too, in
`HTGeometry/ValuationInertiaIntermediateUnramified.lean`:

```text
ramificationIdx_intermediateCentre_eq_one_of_inertia_trivial
    ** an unramified place stays unramified in every intermediate field **
```

`|I_F| = e · |I_M|` with `|I_F| = 1` leaves `e = 1`.  So both halves of step 2 are general:

* at the branch place, inertia sits inside the block stabiliser (transposition argument), and
  `ramificationIdx_fixedField_eq_one_of_inertia_le` gives `e = 1`;
* away from the branch locus, inertia is trivial, and the new theorem gives `e = 1`.

The horizon side of the first half is instantiated (`CriticalBlockFieldUnramified`).  The horizon
side of the second needs only `Nat.card (W.inertiaSubgroup F) = 1` at the non-Schur height-one
primes of the chart ring — which is `E1`
(`isUnramifiedAt_of_aeval_derivative_notMem`) read through
`natCard_inertiaSubgroup_eq_ramificationIdxIn`, plus the localization of the chart ring at an
arbitrary height-one prime.

### Recorded obstruction for step 3's discriminant input

`SCE_k` consumes `IsUnit (Algebra.discr R e)`.  The natural bridge from "unramified everywhere" is
`disc = ± N(p'(x))`, but **mathlib's `Algebra.discr_powerBasis_eq_norm` is stated only for a FIELD
base** (`[Field K] [Field L]`), so it does not apply to the slice polynomial ring.  The ring-level
route is the trace-form one: `differentIdeal = ⊤` says the dual lattice is the ring itself, i.e. the
trace form is unimodular, i.e. the discriminant is a unit.  The corpus's
`SplitFiniteAlgebraDiscriminant.discr_ne_zero_iff_traceForm_nondegenerate` is the field-level half of
that dictionary; the ring-level statement is the piece to build.

Together with `isUnit_of_forall_notMem_isPrime` (which turns "no height-one prime contains the
discriminant" into "the discriminant is a unit" over a UFD), that is the whole of step 3's input.
Recorded so no session assumes mathlib supplies the ring-level identity.

## CORRECTION — step 3 must use the FIELD form of `SC_k`, not the ring form (2026-08-23)

`rank_eq_one_of_isUnit_discr_mvPolynomial` (`SCE_k`) takes `[Module.Free (MvPolynomial (Fin k) K) B]`
together with a basis.  Applying it to the slice means producing a **basis of the integral closure of
`K[w₁,…,w_{L-2}]` in the block field**.  For `k ≥ 2` that is Quillen–Suslin (projective modules over
a polynomial ring are free) — not in mathlib, and not something to walk into by accident.

The card's own 2026-08-18 programme already avoids this, and the next session should follow it:

```text
SC_k, FIELD form:  𝔽 = K(u_1,…,u_{k-1});  a finite extension of 𝔽(u_k) unramified at every
                   height-one prime of 𝔽[u_k] is a CONSTANT extension 𝔽'(u_k);  the Gauss
                   valuation transports unramifiedness of 𝔽'/𝔽 to every height-one prime of
                   K[u_1,…,u_{k-1}];  induct.
```

Every step there works over `𝔽[u_k]`, a **PID**, where finite torsion-free modules are free
automatically — so no Quillen–Suslin is needed, and the ring form of `SC_1`
(`rank_eq_one_of_isUnit_discr_algClosed`, already Lean) applies after base change to `𝔽`'s algebraic
closure.  What the tree does not yet have is the field-form statement and the Gauss-valuation
transport between induction steps.

So step 3's remaining work is, precisely:

```text
(a)  SC_1 field form over a general char-0 base field: unramified over 𝔽[u] ⟹ constant extension
(b)  Gauss-valuation transport: unramifiedness of the constant part over K[u_1,…,u_{k-1}]
(c)  the induction assembling (a) and (b) into the field form of SC_k
(d)  the horizon's slice presentation feeding it
```

and the ring-level trace-form identity recorded in the previous entry is then **not needed** — over a
PID the discriminant question is the classical one that `rank_eq_one_of_isUnit_discr_algClosed`
already answers.

## `(b)`'s first brick: the Gauss prime is unramified (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/GaussPrimeUnramified.lean`, axiom-clean and wired:

```text
ramificationIdx'_map_C_eq_one
    ** q ∋ π ∉ q²  ⟹  ramificationIdx' q (q · R[X]) = 1 **
```

Membership in an extended ideal `I · R[X]` is coefficientwise (`Ideal.mem_map_C_iff`), so contracting
the constant coefficient returns the base statement.  Two neighbouring facts are already mathlib:
`Ideal.isPrime_map_C_of_isPrime` (the Gauss prime is prime) and
`Ideal.polynomialQuotientEquivQuotientPolynomial` (its residue ring is `(R ⧸ q)[X]`).

This is the algebraic form of "the Gauss valuation has ramification index one" — the transport step
of the field-form induction for `SC_k`, and the reason that induction never needs freeness of an
integral closure over a multivariable polynomial ring.

## `(a)`'s mechanism: split roots differ by constants (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/SplitRootUnitDifference.lean`, axiom-clean and wired:

```text
isUnit_sub_of_isUnit_eval_derivative    r - a is a unit whenever p'(r) is
exists_C_of_isUnit_sub                  over F[u] those differences are CONSTANTS
```

Each root difference is a factor of `p'(r) = ∏_{a ≠ r} (r - a)`
(`Polynomial.eval_multiset_prod_X_sub_C_derivative`), so it divides a unit; over a polynomial ring
the units are the nonzero constants (`Polynomial.isUnit_iff`).

This is the mechanism of `SC_1`'s **field** form.  With `𝔽̄` the algebraic closure of the base field,
an everywhere-unramified cover splits over `𝔽̄(u)`, its roots lie in `𝔽̄[u]` and — by the above —
differ by constants; in characteristic zero, `n·r₁ = Σ rᵢ − Σ cᵢ` with `Σ rᵢ ∈ 𝔽(u)` exhibits
`r₁ ∈ 𝔽(u) + 𝔽̄`, so `E = 𝔽(u)(r₁) = 𝔽(γ)(u)` is a **constant** extension.  That is `(a)`, and its
only remaining pieces are the splitting/integrality of the roots and the characteristic-zero average.

### `(a)`'s averaging step

Added to the same module, axiom-clean:

```text
exists_mem_add_mem_of_sum_mem
    ** sum in B, spread in C, characteristic zero  ⟹  a member lies in B + C **
```

With `B` the base rational function field and `C` the constants, this is exactly the passage from
"the roots differ by constants" to "one root is (base) + (constant)", hence `E = 𝔽(γ)(u)`.

`(a)` now needs only its two analytic-free inputs: that an everywhere-unramified cover splits after
base change to `𝔽̄` (this is `rank_eq_one_of_isUnit_discr_algClosed`, already Lean) and that the
roots are integral over `𝔽̄[u]` (normality of the polynomial ring).  The algebraic skeleton —
unit differences, constancy, averaging — is complete.

## `(b)` IS COMPLETE: ramification is unchanged by a free variable (2026-08-23)

`HTGeometry/GaussPrimeUnramified.lean`, axiom-clean and wired:

```text
map_C_le_map_C_iff        I·R[X] ≤ J·R[X]  ↔  I ≤ J
ramificationIdx'_map_C
    ** ramificationIdx' (q·R[X]) (Q·S[X]) = ramificationIdx' q Q **
```

`ramificationIdx'` is `sSup {n | map p ≤ P^n}`, and adjoining a free variable carries that set
bijectively: extension commutes with the algebra map (`Ideal.map_map`), commutes with powers
(`Ideal.map_pow`), and reflects inclusion (`map_C_le_map_C_iff`, from the coefficientwise
description `Ideal.mem_map_C_iff`).  So the two suprema are suprema of the *same* set.

This is `(b)` in full generality — the Gauss transport step of the `SC_k` field-form induction:
unramifiedness of `𝔽'(u_k)/𝔽(u_k)` at the Gauss prime of `q` **is** unramifiedness of `𝔽'/𝔽` at `q`.
Nothing about valuations or completions is needed; it is an identity of two suprema.

Step 3's ledger is now: `(a)` mechanism complete (unit differences, constancy, averaging) with two
structural inputs left; `(b)` **COMPLETE**; `(c)` the induction assembling them; `(d)` the horizon
slice presentation.

## The exact bridge between `SCE_k` and the ramification statements (2026-08-23)

`SCE_k` is stated in **discriminant** form (`HasEtaleRankOne R`: every domain finite free over `R`
with unit discriminant has rank one) while steps 1–2 and `(b)` are in **ramification** form.  The
bridge is one direction of the classical Dedekind discriminant theorem:

```text
q unramified in B  ⟹  disc(B/A) ∉ q          (hence, over a UFD, disc is a unit)
```

and its proof needs one further lemma, also absent from mathlib:

```text
discriminant base change:  (disc_A b)  mod p  =  disc_{A/p} (b mod pB)
```

after which the corpus's own field-level dictionary finishes it:
`SplitFiniteAlgebraDiscriminant.discr_ne_zero_iff_traceForm_nondegenerate` — a finite étale algebra
over a field has nondegenerate trace form, hence nonzero discriminant — and
`isUnit_of_forall_notMem_isPrime` (built this session) converts "in no height-one prime" to "unit".

Searched and confirmed absent: mathlib has no Dedekind discriminant theorem
(`Mathlib/NumberTheory/RamificationInertia/*` and `DedekindDomain/Different.lean` mention `discr`
only in `isIntegral_discr_mul_of_mem_traceDual`) and no `discr` base-change lemma
(`RingTheory/Discriminant.lean`).

**Consequence for the plan.**  `Module.Free` for the integral closure over a multivariable polynomial
ring is Quillen–Suslin and must be avoided; the field-form induction avoids it because each level's
base `𝔽[u_k]` is a PID, where finite torsion-free modules are free.  With `(b)` complete
(`ramificationIdx'_map_C`) and `(a)`'s mechanism complete
(`isUnit_sub_of_isUnit_eval_derivative`, `exists_C_of_isUnit_sub`, `exists_mem_add_mem_of_sum_mem`),
the two named builds above are what remain before `(c)` can be assembled.

## One of the two named gaps is CLOSED: discriminant base change (2026-08-23)

`formal/GaloisForLFunctions/HTGeometry/DiscriminantBaseChange.lean`, axiom-clean and wired:

```text
algebra_trace_baseChange   trace_S (S ⊗ B) (1 ⊗ x) = algebraMap A S (trace_A B x)
discr_baseChange           discr_S (b.baseChange S) = algebraMap A S (discr_A b)
```

mathlib has `LinearMap.trace_baseChange` for the *linear* trace and neither statement for the algebra
trace or the discriminant.  Both follow at once: multiplication by `1 ⊗ x` **is** the base change of
multiplication by `x` (`Algebra.TensorProduct.tmul_mul_tmul`), so the trace matrix in the
base-changed basis is the entrywise image of the trace matrix, and the structure map carries its
determinant.

So the Dedekind discriminant criterion now needs only its second half: reducing modulo `p` gives the
discriminant of the fibre `B ⊗ κ(p)`, and the corpus's
`SplitFiniteAlgebraDiscriminant.discr_ne_zero_iff_traceForm_nondegenerate` says that vanishes exactly
when the fibre's trace form degenerates — i.e. when `p` ramifies.  With
`isUnit_of_forall_notMem_isPrime` that yields "unramified everywhere ⟹ unit discriminant", which is
the last input `SCE_k` needs from the ramification side.

### The Dedekind criterion's interface, in one line

Added to the same module, axiom-clean:

```text
discr_mem_iff_discr_quotient_eq_zero
    ** p contains disc_A b  ↔  disc_{A/p} (b.baseChange (A/p)) = 0 **
```

so the criterion is now purely a **field-level** question about the fibre: over a maximal `p`, the
fibre `B ⊗ (A/p)` is an algebra over a field, and the corpus's
`SplitFiniteAlgebraDiscriminant.discr_ne_zero_iff_traceForm_nondegenerate` turns the vanishing of its
discriminant into degeneracy of its trace form.  Everything below the field level — base change of
the trace, of the discriminant, and the passage from "in no height-one prime" to "unit"
(`isUnit_of_forall_notMem_isPrime`) — is now Lean.

## BOTH named gaps are closed: the Dedekind discriminant criterion (2026-08-23)

`HTGeometry/DiscriminantBaseChange.lean` now carries the whole criterion, axiom-clean and wired:

```text
algebra_trace_baseChange              trace commutes with base change
discr_baseChange                      discriminant commutes with base change
discr_mem_iff_discr_quotient_eq_zero  p ∋ disc  ↔  the fibre discriminant vanishes
discr_notMem_ker_of_split_fibre       a SPLIT fibre forces algebraMap (disc) ≠ 0
discr_notMem_of_split_fibre           ** hence p ∤ disc **
```

The last two are stated with an **abstract residue field** `κ` and a kernel hypothesis rather than
with `A ⧸ p`: phrasing them over the quotient makes the instance search for
`Algebra (A⧸p) ((A⧸p) ⊗[A] B)` exhaust 2M heartbeats, while the abstract form elaborates in seconds.
Recorded as the rule for this lane.

The proof composes the two base-change theorems with the corpus's own
`SplitFiniteAlgebraDiscriminant.discr_ne_zero_of_algHom_family` — a split finite algebra over a field
has discriminant a unit, because it is isomorphic to `κⁿ`, whose discriminant is `1`.

**Step 3's ramification-side input is therefore complete**: unramified (split fibres) at every
height-one prime ⟹ the discriminant lies in no height-one prime (`discr_notMem_of_split_fibre`) ⟹ the
discriminant is a unit (`isUnit_of_forall_notMem_isPrime`) ⟹ `SCE_k` applies.  What remains of `(4)`
is `(a)`'s two structural inputs, `(c)`'s induction and `(d)`'s horizon slice presentation.

## Corpus correction and exact chart identification (2026-08-25)

Mandated corpus audit found that the preceding `SC_k` programme duplicates a theorem already in
the tree.  `HTGeometry/AffineSpaceEtaleRankOne.lean` proves

```text
rank_eq_one_of_isUnit_discr_mvPolynomial
```

for arbitrary finite-dimensional affine space over an algebraically closed field.  Thus the
field-form `SC_1`, Gauss transport, and induction listed above are not remaining obligations for
this card.

Three exact infrastructure modules now close the coordinate-ring side of step 3:

```text
PolynomialFractionIntegralRoot.lean
  exists_polynomial_eq_of_monic_eval₂_eq_zero
  exists_polynomial_eq_of_monic_map_isRoot
    roots in Frac(F[u]) integral over F[u] already lie in F[u]

LocalizationAwayRingEquiv.lean
  awayRingEquiv
    a ring equivalence carrying f to g transports Localization.Away f to Localization.Away g

CriticalObservationTorusChartEquiv.lean
  criticalObservationPolynomialTorusEquiv_marked
  criticalObservationChartTorusEquiv
    criticalObservationChartRing K m n ≃+* TorusChart K (n+m-2)
```

All three leaf modules pass targeted builds.  Every new declaration is axiom-clean with only
`[propext, Classical.choice, Quot.sound]`, and all are wired into the `HTGeometry` umbrella without
building that umbrella.

Remaining exact obligation for `(4)`: instantiate the block intermediate field on this chart,
prove it unramified at non-Schur height-one primes, and assemble slice/base-change plus marked
total-ramification argument into unconditional primitivity.  Schur-place unramifiedness,
affine-space rank-one theorem, actual chart equivalence, total-ramification lower bound,
transposition, and Jordan capstone are now present.

## Exact analytic chart bridge (2026-08-25)

The coordinate-ring identification now reaches the topological chart used by the cyclic-cover
reduction.  Four axiom-clean additions are wired into `HTGeometry`:

```text
AlgebraSpectrumEquiv.lean
  AlgSpec.precomp
  AlgSpec.homeomorphOfAlgEquiv
    a complex-algebra equivalence induces the contravariant homeomorphism on complex points

CriticalObservationTorusChartEquiv.lean
  criticalObservationChartTorusAlgEquiv
    criticalObservationChartRing K m n ≃ₐ[K] TorusChart K (n+m-2)

TorusChartComplexPoints.lean
  torusChartComplexPointHomeomorph
    AlgSpec (TorusChart ℂ k) ≃ₜ (ℂˣ × ℂˣ × Multiplicative (Fin k → ℂ))

CriticalObservationComplexPoints.lean
  criticalObservationComplexPointHomeomorph
    AlgSpec (criticalObservationChartRing ℂ m n) ≃ₜ
      ComplexTorusAffineChart (n+m-2)

CriticalObservationConnectedCover.lean
  criticalObservationAnalyticProjection_isCoveringMap
  criticalObservationConnectedFiniteCover_exists_nontrivial_cyclic_character
    every nontrivial connected finite cover of the actual observation chart yields the exact
    nontrivial cyclic torus character and nondivisible exponent pair
```

The inverse continuity in `torusChartComplexPointHomeomorph` is not assumed: every fixed localized
element is represented by a fixed numerator and denominator, polynomial evaluation is proved
continuous by induction, and the denominator is nowhere zero because it lies in the localized
power submonoid.  Targeted leaf builds pass.  Axiom audit of every new public declaration reports
only `[propext, Classical.choice, Quot.sound]`; no umbrella build was run.

Thus the torus `pi_1`, finite connected-cover cyclic-character theorem, actual observation-chart
algebra, actual observation-chart complex topology, and covering transport are all joined.
Remaining exact producer is narrower: construct the integral model of the fixed block intermediate
field as a nontrivial connected finite covering of this `AlgSpec`, then identify its cyclic
character with the source Kummer relation killed by the two already-formalized source valuations.
No chart-identification, point-topology, cover-transport, or cyclic-reduction gap remains.
