# The reciprocal jet tower is reversal-self-Legendre

- **ID:** `projective-horizon-reversal-self-legendre-tower`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT LAGRANGIAN POLARIZATION TOWER
- **Scientific status:** `[PROVED ON PAPER] [FORMALIZED] [NOVELTY PROVISIONAL] [SIGNIFICANCE CANDIDATE]`
- **Formal status:** fully formalized in Lean 4
- **Parents:** `projective-horizon-logarithmic-vacuum-duality`,
  `projective-horizon-finite-jet-page-transition`, `hypertranscendental-horizon-q-system`
- **Lane:** source-pure hypertranscendental geometry; no carrier, time, or evolution

## Theorem

Let `K` be a characteristic-zero field and let

```text
X(t)=x_0+x_1t+...+x_Nt^N,       x_0!=0,
Y(t)=X(t)^-1 mod t^(N+1)=y_0+y_1t+...+y_Nt^N.              (1)
```

On the unit-jet chart `U_N=Spec K[x_0,x_0^-1,x_1,...,x_N]`, define

```text
S_N(X)=[t^N] log(X/X(0)),       N>=1.                       (2)
```

Give `T*U_N` the reversed coefficient momenta `pi_0,...,pi_N`.  Then:

1. **Reciprocal gradient.**  The full gradient of `(2)` is the reversed reciprocal jet:

   ```text
   partial S_N/partial x_i = y_(N-i)=pi_i,    0<=i<=N.      (3)
   ```

   Consequently the graph of truncated inversion, after coefficient reversal, is the exact
   Lagrangian graph `Graph(dS_N)`.

2. **Reversal-self-Legendre duality.**  Regard the dual chart as

   ```text
   U_N^vee=Spec K[pi_N,pi_N^-1,pi_0,...,pi_(N-1)]
   ```

   and form its unit series `Y(t)=sum_(j=0)^N pi_(N-j)t^j`.  The ordinary Legendre transform of
   `S_N` is the same logarithmic-coefficient potential in this reversed dual chart:

   ```text
   S_N^*(pi)
     =sum_(i=0)^N x_i pi_i-S_N(X)
     =S_N(Y).                                                (4)
   ```

   On the reciprocal graph, `S_N(Y)=-S_N(X)`.  Thus the operation `X -> Y`, together with
   coefficient reversal between coordinates and momenta, is an involutive exact-Lagrangian
   duality.

3. **Every critical horizon is a partial Legendre projection.**  Let `m,n>=1` with
   `m+n=N+1`.  Fix the raw tail `x_m,...,x_N` and the first `m` momenta

   ```text
   pi_i=q_(N-i),       0<=i<m.                              (5)
   ```

   The fiber of this partial cotangent projection is precisely the critical `(m,n)`
   raw/reciprocal horizon fiber.  Equivalently, it is the critical scheme in the low variables
   `x_0,...,x_(m-1)` of

   ```text
   S_N(X)-sum_(i=0)^(m-1) x_i q_(N-i).                      (6)
   ```

4. **The earlier finite laws are invariants of one polarization atlas.**  A generic partial
   projection in part 3 has degree

   ```text
   choose(N+1,m).                                           (7)
   ```

   Its ramification determinant is, up to a nonzero unit and row reversal, the rectangular Schur
   function `s_((n^m))`.  As `(m,n)` varies, these determinants obey the static `A_infinity`
   Q-system.  Hence the Page transition, binomial multiplicity, Schur caustics, rank-level
   duality, and Q-system are not separate analogies: they are the degree, ramification, duality,
   and Pluecker compatibility data of the partial-polarization atlas of `Graph(dS_N)`.

5. **Hypertranscendental section.**  If the coefficients in `(1)` are the first `N+1` jet
   coordinates of a hypertranscendental source, then they are algebraically generic at every
   finite `N`.  The source therefore defines a compatible section through the entire tower which
   lies algebraically off every finite rectangular ramification divisor.

## Proof

For a variation `delta X=sum_i delta x_i t^i`, formal logarithmic differentiation gives

```text
delta S_N=[t^N](Y delta X)
         =sum_(i=0)^N y_(N-i) delta x_i.                    (8)
```

The normalization by `X(0)` contributes only in degree zero and therefore does not alter `(8)`
when `N>=1`.  This proves `(3)`.  A graph of a differential is exact Lagrangian.  Directly, its
symplectic form is

```text
sum_i delta x_i wedge delta pi_i
  =[t^N](delta X wedge delta Y),                            (9)
```

and `delta Y=-Y^2 delta X` makes `(9)` vanish.

The inverse relation gives

```text
sum_(i=0)^N x_i pi_i=[t^N](XY)=0                           (10)
```

because `N>0`.  Also `log Y=-log X mod t^(N+1)`, so

```text
S_N(Y)=-S_N(X).                                             (11)
```

Substituting `(10)` and `(11)` into the definition of the Legendre transform proves `(4)`.  Since
truncated inversion is an involution, the reversed duality is involutive.

For part 3, `pi_i=y_(N-i)`.  The range `0<=i<m` is exactly the reciprocal tail
`y_n,...,y_N`, in reverse order, because `n=N+1-m`.  Fixing `(5)` is therefore exactly the critical
horizon observation problem, and `(3)` turns its equations into the critical equations of `(6)`.

Part 4 is the conjunction of the proved critical finite-degree theorem, the Hessian row-reversal
theorem, the rectangular Schur-caustic theorem, and the all-depth Desnanot--Jacobi Q-system.  Part
5 follows from finite jet algebraic independence and the proved nonvanishing of every rectangular
Schur amplitude at an algebraically independent reciprocal jet.  `QED`

## Physical and topological meaning

The source does not move through derivative order.  Instead, every finite resolution presents one
and the same reciprocal constraint in a different cotangent polarization.  What looked separately
like information release, vacuum multiplicity, a massless locus, particle/hole duality, and an
integrable lattice is one static object:

```text
hypertranscendental geometry
  = a compatible tower of exact Lagrangian reciprocal graphs
    equipped with all partial polarization maps,
    whose branch divisors form a nonvanishing Q-system.      (12)
```

The closest physical language is therefore not time evolution or a black-hole interior.  It is a
polarization-independent vacuum constraint: different observers fix complementary source and
momentum packets of the same exact Lagrangian state relation.  The Page-type law is a projection
degree transition, not evaporation; the Schur divisor is a caustic of polarization, not a spacetime
singularity; the Q-system is the incidence topology of the polarization atlas, not a Hamiltonian
flow.

This theorem does not construct a Hilbert space, quantization, entropy, causal structure, or
holographic bulk.  Those interpretations would require additional structure.

## Novelty and significance audit

Formal logarithms, exact Lagrangian graphs, Legendre transforms, reciprocal power series,
Grassmannian Schur calculus, and Q-systems are classical separately.  Homaloidal and multiplicative
Legendre theories study birational logarithmic gradients, but they do not by themselves supply the
finite reciprocal-jet tower or its complete family of partial horizon projections.

A targeted search found no theorem identifying the coefficient potential `(2)`, its reversed
reciprocal gradient `(3)`, all partial projections `(5)`, their binomial degrees, their rectangular
Schur branch divisors, and their Q-system as one hypertranscendental constraint tower.  This is a
provisional novelty verdict, not proof of absence from the literature.

The synthesis gives a canonical answer to the requested nature question and a reusable geometric
object.  It does not yet classify hypertranscendental functions or distinguish two such functions.
The adjacent all-rank theorem now proves that the partial projections have full symmetric
monodromy, strengthening this tower into a maximally braided polarization atlas.  The present
theorem still does not by itself clear the Fields-Medal completion bar.

## RH impact

For zeta, the theorem supplies a compatible exact-Lagrangian section at every finite jet order and
organizes all reciprocal observation fibers into one polarization atlas.  The construction remains
invariant under target translation of the source, while RH is not.  It therefore has no direct RH
consequence.  A useful RH refinement would have to add an Euler/functional-equation orientation to
the Lagrangian section or to its vanishing cycles without destroying the partial-polarization
relations.

## Formal verification

`ProjectiveHorizonLogPotential.lean` proves the full reversed-reciprocal logarithmic gradient `(3)`,
the inverse logarithm law `(11)`, the reversed self-Legendre identity `(4)`, and the exact partial
cotangent/critical-horizon correspondence `(5)--(6)`.
`ProjectiveHorizonExactLagrangian.lean` certifies that coefficient residue is exactly the reversed
cotangent dot product, the positive-degree vanishing `(10)`, that the residue symplectic form is
exactly the reversed canonical cotangent sum, and isotropy `(9)`.
`ProjectiveHorizonPolarizationTower.lean` adds the half-dimension theorem and the single compatible
hypertranscendental tower object, with exact raw/reciprocal inversion, every finite amplitude,
noncausticity, boundary values, the all-rank Q-system, and caustic zero propagation.

`ProjectiveHorizonLandauGinzburgDuality.lean`, `ProjectiveHorizonPageTransition.lean`,
`ProjectiveHorizonCriticalMultiplicity.lean`, and `ProjectiveHorizonSchurCaustic.lean` certify the
Hessian, row reversal, finite degree, and Schur-caustic parts.  The all-rank and source-generic
claims are certified by `ProjectiveHorizonAllRankQSystem.lean`.

The three new modules elaborate directly and their dedicated Lake targets pass.  Axiom audits of
the Legendre, isotropy, tower inversion, noncausticity, and Q-system theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.  The formal lint gate passes.  No full build was run.
