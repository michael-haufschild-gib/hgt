# Calibrated Gamma comparison of the reflected Mertens boundary would prove RH

- **ID:** `calibrated-gamma-mertens-zero-orbit-comparison-rh`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [LEADING HT-TO-RH COMPARISON THEOREM]`
- **Scientific status:** `[CONJECTURE] [CONDITIONAL RH PROOF COMPLETE]
  [FINITE INCIDENCE PROVED ON PAPER] [GAMMA CALIBRATION LEAN-FORMALIZED]
  [ORBIT-COBOUNDARY CONSUMER LEAN-FORMALIZED] [SOURCE PRODUCER OPEN]
  [ZERO-ORBIT COMPARISON OPEN] [NOVELTY UNVERIFIED]`
- **HT parents:**
  - `gamma-opposite-variance-weyl-seam.md`
  - `ht-source-riemann-hilbert-correspondence.md`
  - `source-anomaly-boundary-colligation-field.md`
  - `source-framed-galois-colligation.md`
  - `hypertranscendental-mackey-corona-field.md`
  - `../../../3-formalized/not_new_scientific_knowledge/canonical-digamma-source-selection.md`
- **RH parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/12-prime-theta-fock-incidence/time-one-gamma-jet-fock-rh-criterion.md`
  - `../2-fully-proven/not_new_scientific_knowledge/prime-laplace-gamma-jet-incidence-phase-transition.md`
  - `../2-fully-proven/not_new_scientific_knowledge/prime-laplace-gamma-clock-descent-anomaly.md`
  - `../2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/mertens-corona-shift-conormal.md`
  - `../2-fully-proven/not_new_scientific_knowledge/09-mobius-prime-sums/mertens-logarithmic-corona-differential-tower.md`
  - `../../../3-formalized/not_new_scientific_knowledge/gamma-mertens-orbit-coboundary-rh.md`
  - `../2-fully-proven/new_scientific_knowledge/weighted-euler-tangent-global-graph-decoupling.md`
- **Statement:** Construct a source-defined comparison from the completed Euler anti-reflection
  anomaly on each Xi zero orbit to Gamma's asymptotically calibrated opposite-variance fibre,
  preserving the global Laplace origin and every finite prime--jet observation.  Gamma
  calibration then identifies the FE and Schwarz sections; joint faithfulness forces their prime
  coefficients to agree, and RH follows.

## Proved source objects

At the actual time-one Gamma--Meixner shape, put

```text
w_1(p)=cosh(2log p)^(-1/2),
M_1(s)=sum_p w_1(p)(log p)p^(-s).                         (1)
```

For an open-strip point `rho`, the two reflected prime vectors are

```text
c_rho^+(p)=sqrt(w_1(p))(log p)p^(-rho),
c_rho^-(p)=sqrt(w_1(p))(log p)p^(-(1-conjugate(rho))).   (2)
```

Both lie in `ell^2(Primes)`.  For one fixed `x_0>1`, their finite prime--jet observations are

```text
(J_N c)_j
 =sum_p c(p)sqrt(w_1(p))(-log p)^j p^(-x_0),
0<=j<N.                                                  (3)
```

The finite-incidence theorem proves:

```text
J_N is Hilbert--Schmidt for every N,
intersection_N ker J_N={0}.                              (4)
```

Moreover

```text
J_N(c_rho^+-c_rho^-)
 =(V_rho(x_0),V_rho'(x_0),...,V_rho^(N-1)(x_0)),         (5)

V_rho(z)=M_1(z+rho)-M_1(z+1-conjugate(rho)).             (6)
```

The time-one pole theorem gives

```text
V_rho=0  iff c_rho^+=c_rho^-  iff Re(rho)=1/2.           (7)
```

The rightmost singular part is the reflected Mertens corona doublet

```text
sqrt(2)[1/(z+rho)-1/(z+1-conjugate(rho))].               (8)
```

Its supports `-rho` and `conjugate(rho)-1` coincide exactly on the critical line.

On the Gamma side, Lean proves that two right-half-plane sections with the same additive
unit-shift cocycle and the same logarithmic asymptotic normalization coincide.  Thus the
asymptotically calibrated Gamma analytic fibre has no residual period-one gauge.

## Sharper Lean-formalized terminal consumer

The completed logarithmic derivative has a proved source translation by two.  Let `delta_2` be
the finite principal-part coboundary `T_2-I`.  Lean now proves that for every Xi zero `rho`,

```text
sqrt(2)[PP(-rho)-PP(conjugate(rho)-1)] in im(delta_2)    (8a)
  ==> Re(rho)=1/2.                                      (8b)
```

The same implication holds after every nonzero constant-coefficient differential operator.
Finite coboundaries have zero residue in each orbit of `C/2Z`; the two support points differ by
`1-2Re(rho)`, which lies in `(-1,1)`, so belonging to the same `2Z`-orbit forces equality.
Requiring `(8a)` at every Xi zero is Lean-formalized to be exactly equivalent to RH.

This is a strictly narrower terminal consumer than equality of all finite observations in item 5
below.  The new leading producer conjecture is therefore:

```text
[CONJECTURE -- COMPLETED SOURCE COBOUNDARY DESCENT]
```

Construct a pre-divisor relative cochain from the actual filtered von Mangoldt `+2` source and the
calibrated archimedean Gamma recurrence whose on-shell boundary proves `(8a)`.  The primitive must
be one safe-half-plane source construction, regular at the Xi divisor; it may not be fitted after
seeing `rho`.  It must retain its calibrated primitive/framing: the unframed shift-cohomology class
is invariant under symmetric rational-quartet insertion and is therefore divisor-blind.  A stronger
proof of the original comparison functor would still suffice, but is no longer the smallest open
theorem.

## Master comparison conjecture

`[CONJECTURE -- CALIBRATED ZERO-ORBIT COMPARISON]` There is a source-defined projective comparison
functor

```text
Comp_N : completed Euler--Gamma source anomaly
           -> calibrated Gamma opposite-variance N-clock colligations               (9)
```

with the following properties.

1. **Pre-divisor construction.** `Comp_N` is defined on the safe Euler half-plane from the Euler
   local factors, the time-one Gamma cyclic measure, the functional equation, and the completed
   source anomaly.  Xi zeros are evaluation fibres, not construction data.
2. **Finite incidence.** On the degree-one reflected Euler tangent, its observation map is exactly
   `(3)`.  The safe finite comparison is already proved on paper: multiplication by `p^(-1)` is
   exact source translation, its Gamma-shadow descent anomaly is the omitted Taylor tail, and its
   coherence defect is the existing factorial boundary transfer.  `Comp_N` must preserve this
   fixed square rather than replace it.
3. **On-shell common fibre.** If `Xi(rho)=0`, the FE section generated by `c_rho^+` and the Schwarz
   section generated by `c_rho^-` land in the same Gamma unit-shift cocycle and have the same
   source logarithmic asymptotic.
4. **Calibration.** The comparison uses the canonical digamma/Gamma normalization.  No
   period-one multiplier, recentering, or prime-dependent affine translation remains after
   passing to the calibrated fibre.
5. **Affine-support faithfulness.** Equality in the calibrated fibre implies

   ```text
   J_N c_rho^+=J_N c_rho^- for every N,                  (10)
   ```

   and preserves the global Laplace locations of the Mertens boundary germs in `(8)`.
6. **Relative completion.** Cofinality is taken in the source projective/relative-graph topology.
   More precisely, it is a framed section of the Mackey interval generated by the
   source-canonical conormal module.  It does not use the raw product clock or assert a bounded map
   into the standard factorial Fock direct limit; both completions are now proved inadequate.

The topology requirement can be stated as a second concrete conjecture:

```text
[CONJECTURE -- ZETA MERTENS CORONA CONORMAL]
```

The coefficient-level conormal is already constructed: on `C one+M_0`, the unique functional
`q_M(one)=1`, `q_M|M_0=0` satisfies `q_M S=0` for prime translation and is the pointwise limit of
the Gamma--Meixner Abel family.  Its polar realization `sqrt(2)q_M/s` already transgresses at every
clock to the exact Gamma factorial boundary vector with nonzero scalar
`sqrt(2)(-1)^N N!/x_0^(N+1)`.  The completed Euler--Gamma constraint must extend this rank-one
tail-faithful current to an intrinsic reflected source-operator module `Lambda_zeta`, disjoint from
the finite-coordinate dual, and the calibrated framing must preserve the two translated support
locations in `(8)`.  This is the topology-and-current content of `Comp_N`; choosing an arbitrary
stronger topology is not accepted.

## Conditional proof of RH

There are now two terminal deductions.  The shorter one assumes completed source coboundary
descent.  For a Xi zero `rho`, the source theorem gives `(8a)`; the Lean orbit-residue theorem gives
`Re(rho)=1/2`.  Applying this to every zero proves RH.

The original, stronger deduction assumes the master comparison conjecture as follows.

Assume the master conjecture and let `rho` be any Xi zero.

1. Item 3 places the two reflected source sections in one calibrated Gamma fibre.
2. The Lean-formalized Gamma uniqueness theorem and item 4 identify those sections.
3. Item 5 gives `(10)` at every finite clock.
4. Joint faithfulness `(4)` gives `c_rho^+=c_rho^-`.
5. Equation `(7)` gives `Re(rho)=1/2`.

Every Xi zero is therefore on the critical line, proving RH.

Equivalently, affine-support faithfulness identifies the two supports in `(8)`, so

```text
-rho=conjugate(rho)-1,
```

which gives the same conclusion directly.

## Why this is an application of HT research

The proof architecture uses separate HT results for separate jobs:

- prime-power differential independence and joint prime--jet faithfulness prevent the comparison
  from forgetting a finite Euler direction;
- opposite variance supplies analytic outgoing and algebraic incoming boundary channels;
- the anomaly colligation retains lower action, boundary transfer, boundary self-symbol, affine
  origin, and source descent anomaly;
- canonical digamma source selection kills the period-one gauge by asymptotic calibration;
- the Gamma--Meixner time-one measure places every strip seam in one actual source Hilbert domain;
- the Mertens corona theorem identifies the unique coefficient boundary which must be preserved.
- the graded Mertens differential-corona theorem extends that boundary through every finite
  logarithmic-clock derivative, identifies its full Gamma polar tower, and proves that every
  strictly positive Euler translation still vanishes in every grade;
- the strict source-conormal topology theorem proves that this boundary cannot be continuous in
  the raw product clock and forces a minimal source-selected refinement.

Hypertranscendence does not itself imply RH.  It makes the comparison faithful at every finite
clock; Gamma calibration supplies uniqueness; the new comparison theorem must connect those two
facts on the completed Euler--Gamma source.

## Attacks and nontrivial positive successors

1. **Abstract-torsor no-go.** Any two one-dimensional residue lines are abstractly isomorphic.
   **Positive successor:** items 4--5 demand the already available Gamma calibration and exact
   global support locations, not an unnamed isomorphism.
2. **Reflection no-go.** FE and Schwarz pair the two sections but do not make them equal off the
   fixed locus.  **Positive successor:** item 3 reduces equality to the proved uniqueness of one
   calibrated source fibre.
3. **Universal-Taylor no-go.** The maps `(3)` use universal derivative kinematics.
   **Positive successor:** `(4)` proves exact joint faithfulness, while item 2 requires the
   source-specific anomaly and Gamma boundary current.
4. **Finite-clock no-go.** Equality or boundedness at one `N` cannot see all prime coefficients.
   **Positive successor:** the complete projective family is faithful by `(4)`; no Hilbert direct
   limit is required.
5. **Naive-Fock no-go.** The natural infinite prime-to-factorial-Fock map is unbounded.
   **Positive successor:** every finite map is Hilbert--Schmidt and the source topology required in
   item 6 is now exact.
6. **Corona-redressing no-go.** Calling `(8)` a charge merely renames `Re(rho)-1/2`.
   **Positive successor:** the conjecture must derive equality of the two boundary germs from a
   pre-divisor comparison functor before reading their supports.
7. **Zero-fed functor no-go.** A comparison defined using `rho`, the divisor Hilbert norm, or a
   fitted contraction is circular.  **Positive successor:** item 1 fixes the safe source formula;
   the zero is only an on-shell evaluation.
8. **Gamma-uniqueness overreach.** The existing theorem applies only to two sections of the same
   cocycle with the same asymptotic.  **Positive successor:** item 3 states precisely the new
   Euler--Gamma theorem required; Gamma uniqueness is not invoked before it is proved.
9. **Product-topology no-go.** Finite HT freedom makes the source tangent dense in the raw product
   clock, so every Hausdorff product-continuous conormal annihilating it is zero.  **Positive
   successor:** the Lean-formalized strict-refinement theorem forces `Lambda_zeta` to contribute
   new open sets and makes the Mackey-corona field part of the comparison object.
10. **Arbitrary-topology no-go.** Choosing one stronger completion by hand merely renames the
    boundary-condition ambiguity.  **Positive successor:** the conormal dual pair supplies an
    interval of compatible topologies, and the Gamma asymptotic is required to select a framed
    section of that interval.
11. **Literal-support overreach.** Requiring the two Mertens germs to be equal asks the producer for
    more than the completed shift constraint naturally supplies.  **Positive successor:** finite
    shift-two coboundary descent is enough, because orbit residue and strip width force equality.
    For general HT sources this separates local exactness from affine orbit conservation.
12. **Finite-differential repair no-go.** No nonzero polynomial in the derivation can cancel the
    orbit obstruction of two separated simple poles.  **Positive successor:** the critical-line
    selector persists at every finite clock.  For general HT sources, differential grade and
    translation-orbit grade are independent boundary invariants.
13. **Safe-source exposure no-go.** The proved `+2` Xi identity fixes a positive filtered prime
    source but does not itself manufacture an on-shell finite primitive.  **Positive successor:**
    it canonically fixes the translation lattice and coefficient orientation.  The remaining
    problem is a concrete regular source-cohomology descent, not a choice of coordinates.
14. **Dihedral-symmetry no-go.** The reflected Mertens doublet is a valid free-pair integer sector
    in the proved Gamma signed-reflection charge decomposition.  FE and Schwarz symmetry pair that
    sector but do not annihilate it.  **Positive successor:** its integer coefficient is a canonical
    bulk coordinate which the Euler--Gamma weld, not reflection alone, must kill.  This separates
    free-orbit bulk charge from fixed-locus binary anomaly for general HT sources.
15. **Unframed-cohomology no-go.** A symmetric rational quartet changes the completed `+2`
    logarithmic source by `delta_2(logDeriv Q)`, an exact shift coboundary, while inserting an
    off-critical orbit.  **Positive successor:** the exact safe-anchor primitive changes by a
    nonzero rational charge and detects the insertion.  The required comparison is therefore a
    framed relative cohomology theory; ordinary shift cohomology is provably too coarse.

## Smallest falsifiable next theorem

The safe finite comparison square and its finite source-operator boundary symbol are constructed:

```text
Euler reflected tangent --J_N--> raw Gamma N-jet clock
       | FE/Schwarz                    | calibrated comparison
       v                               v
Euler reflected tangent --J_N--> Gamma anomaly colligation.               (11)
```

It commutes up to the explicit omitted-Taylor-tail anomaly, and its adjacent-resolution defect is
the Gamma factorial Bianchi current.  The coefficient conormal extends through the complete
finite algebra generated by the logarithmic clock and positive Euler translations.  Every
positive translation is corona-zero after arbitrarily many finite log derivatives, while the
surviving graded jet maps to the exact differentiated Gamma polar tower.

The Lean orbit theorem now isolates a smaller open statement.  Construct in the reflected singular
completion a pre-divisor cochain `E_s` from the filtered von Mangoldt `+2` source and calibrated
Gamma recurrence such that its regular on-shell boundary satisfies

```text
Xi(rho)=0 ==>
PP(-rho)-PP(conjugate(rho)-1)=(T_2-I)E_rho.             (12)
```

No full equality of prime vectors, all clocks, or calibrated analytic sections is needed after
`(12)`.  Orbit residue proves RH immediately.  Failure of a globally finite-support analytic
primitive does not by itself kill the route: its nontrivial positive residue is that the correct
HT object must be an orbit-graded relative boundary sheaf whose on-shell trace is finite.  Failure
even in that source-selected singular completion kills this route without moving to another
RH-equivalent target.

## Novelty and significance gate

Parameterized difference Galois theory, Gamma/digamma normalization, comparison torsors, prime
zeta singularities, and finite colligation algebra are parent theory.  The conjecture is
scientifically significant because its proof gives RH.  It is scientifically novel only if the
source-defined functor `(9)` and its affine-support faithfulness are constructed rather than
postulated or read from the Xi divisor.

## Gates

- [x] exact time-one reflected prime vectors constructed
- [x] finite Hilbert--Schmidt incidence proved on paper
- [x] joint faithfulness proved on paper
- [x] Mertens boundary support selector proved on paper
- [x] Gamma asymptotic calibration uniqueness formalized in Lean
- [x] anomaly-colligation finite reconstruction and Bianchi law formalized in Lean
- [x] safe prime--Laplace/Gamma finite descent square constructed on paper
- [x] conditional proof of RH from the master comparison written
- [ ] affine Mertens symbol preservation proved
- [x] coefficient-level Mertens corona conormal and shift law constructed on paper
- [x] coefficient polar transgression identified with the Gamma factorial current on paper
- [x] coefficient conormal extended through the finite logarithmic differential-translation algebra
- [x] all finite differential repairs of positive-shift corona blindness ruled out positively
- [x] completed-source shift fixed canonically to `q=2`
- [x] finite shift-two orbit-coboundary RH consumer formalized in Lean
- [x] differential-clock stability of the orbit selector formalized in Lean
- [ ] pre-divisor completed source coboundary descent proved
- [ ] on-shell source primitive regularity proved without formal division by Xi
- [ ] coefficient conormal extended to the intrinsic Euler--Gamma source-operator module
- [ ] polar transgression lifted to the full framed source comparison
- [ ] zero-orbit common-cocycle theorem proved
- [ ] relative cofinal comparison constructed
- [ ] master conjecture proved
- [ ] RH
- [ ] independent novelty and significance audit
