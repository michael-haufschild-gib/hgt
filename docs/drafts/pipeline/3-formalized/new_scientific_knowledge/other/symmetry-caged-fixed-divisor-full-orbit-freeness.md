# Symmetry-caged fixed-divisor full-orbit freeness

- **ID:** `symmetry-caged-fixed-divisor-full-orbit-freeness`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM (paper) — `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Lane:** general hypertranscendence; constraint-compatible genericity; divisor fibers
- **Statement:** Functional-equation symmetry, Schwarz reality, a prescribed entire
  divisor, and any fixed finite normalization passport remain compatible with maximal
  differential-algebraic independence of the full complex translation orbit.

## Constraint space

Let

`sigma(z)=1-z`, `kappa(z)=conj(z)`,

and let

`E={g in O(C):g(sigma z)=g(z), g(kappa z)=conj(g(z))}`.

This is a real Frechet space.  Let `A subset C` be finite and invariant under the group generated
by `sigma` and `kappa`, and let `nu:A -> N` be invariant under that group.  Write

`E_(A,nu)={g in E:g^(j)(a)=0 for a in A and 0<=j<nu(a)}`.

Let `W` be a nonzero entire function satisfying

`W(1-z)=W(z)`, `W(conj z)=conj(W(z))`.

For `g in E_(A,nu)`, put `F_g=W exp(g)`.

## Theorem `[PROVED HERE]`

A comeager subset of `E_(A,nu)` consists of gauges for which every finite family of distinct
complex translates of `F_g` is differentially algebraically independent over `C(z)`.  Equivalently,

`{T_h F_g:h in C}`

is a differentially algebraically independent family over `C(z)`.

Every such `F_g` has the divisor of `W`, satisfies the two symmetries, and agrees with `W` through
order `nu(a)-1` at every `a in A`.

## Proof

### 1. Symmetry-separated evaluation packets

Fix `m>=1`, a jet order `r`, and one finite support of `R` distinct expanded differential
monomials

`M_j(z,Y)=z^(k_j) prod_(i=1)^m prod_(ell=0)^r Y_(i,ell)^(alpha_(j,i,ell))`.

Put `q=max_j k_j`.  Fix a shift tuple `h^0` in

`Conf_m(C)={(h_1,...,h_m):h_i!=h_j when i!=j}`.

Let `G={1,sigma,kappa,sigma kappa}`.  For any prescribed `N`, one can choose distinct evaluation
points `z_1,...,z_N` so that the `Nm` points

`Q(h^0)={z_a+h_i^0:1<=a<=N,1<=i<=m}`

avoid `A`, avoid the zero set of `W`, have trivial `G`-stabilizer, and have pairwise disjoint
`G`-orbits.

Indeed, choose the `z_a` successively.  Collision with an already selected symmetry orbit, a
nontrivial stabilizer, or a collision between two points in the new row excludes only finitely many
points and real affine lines.  Hitting `A` or a translated zero of `W` excludes a finite union of
finite or discrete sets.  These forbidden sets cannot cover `C`.  Shrinking to a relatively compact
real neighborhood `U` of `h^0` in `Conf_m(C)`, all these separations and nonvanishing conditions
continue to hold for every `h in U`.

### 2. Equivariant passport Hermite lemma

Let `Q={x_1,...,x_L}` be any finite packet with trivial, pairwise disjoint `G`-orbits, disjoint from
`A`.  For every assignment of arbitrary complex derivative jets

`b_(t,n)`, `1<=t<=L`, `0<=n<=r`,

there is a polynomial `p` satisfying

`p(1-z)=p(z)`, `p(conj z)=conj(p(z))`,

`p^(j)(a)=0` for `a in A`, `0<=j<nu(a)`, and

`p^(n)(x_t)=b_(t,n)`.

To prove this, first extend the assigned jets to the full disjoint packet `GQ` by

`b_(sigma x,n)=(-1)^n b_(x,n)`,

`b_(kappa x,n)=conj(b_(x,n))`,

and the composite rule for `sigma kappa`.  Ordinary finite Hermite interpolation followed by
averaging over `G` gives a real-symmetric even polynomial realizing this compatible packet.

The passport constraint costs no freedom.  Set

`H(z)=prod_(a in A) (z-a)^(2 nu(a))`.

Invariance of `A` and `nu`, together with the even total exponent, gives

`H(1-z)=H(z)`, `H(conj z)=conj(H(z))`.

At every `x_t`, multiplication of an `r`-jet by the nonzero jet of `H` is triangular with diagonal
coefficient `H(x_t)!=0`, hence invertible.  Prescribe the unique jets of a polynomial `q` for which
the jets of `Hq` equal the requested `b_(t,n)`, extend them equivariantly, and apply the preceding
Hermite construction.  Then `p=Hq` has all required properties.  A uniform degree bound depending
only on `|A|,nu,L,r` follows from the standard degree-bounded Hermite representative.

Thus, for all `h in U`, one fixed finite-dimensional real vector space `V` of symmetric passport-
vanishing polynomials maps surjectively, as a real-linear map, to the complex `r`-jets at all points
`z_a+h_i`.

### 3. Rank-defect codimension

At a regular evaluation point, the jet of each shifted `F_g` belongs to

`X=(C^x)^m times C^(mr)`.

Let `B_(S,z) subset X^N` be the algebraic locus on which the `N by R` monomial-evaluation matrix

`(M_j(z_a,x_a))_(a,j)`

has rank less than `R`.  Its projective incidence variety consists of pairs `(x,[c])` satisfying

`sum_j c_j M_j(z_a,x_a)=0`, `1<=a<=N`.

For fixed `[c]`, after equal `Y`-monomials are grouped, at least one nonzero coefficient polynomial
in `z` remains, of degree at most `q`.  Since the `z_a` are distinct, at most `q` rows are identically
inactive.  Every other row imposes one nonzero polynomial equation on its independent copy of `X`.
The coefficient vector has projective dimension `R-1`, so

`codim_C B_(S,z) >= N-q-R+1`.                                      (1)

Choose

`N>m+q+R-1`.

Every stratum of a complex Whitney stratification of `B_(S,z)` then has real codimension strictly
greater than `2m=dim_R U`.

### 4. The constrained universal map is a real submersion

Fix `g_0 in E_(A,nu)`.  With `V` supplied by the equivariant passport Hermite lemma, define

`Psi:V times U -> X^N`

by the jets through order `r` of

`W exp(g_0+p)`

at the points `z_a+h_i`.

For fixed `h`, the polynomial direction realizes arbitrary complex jets of `p` at all selected
points.  At a point where `W!=0`, the map from the jet of `p` to the jet of `W exp(g_0+p)` is
triangular, with nonzero diagonal coefficient `W exp(g_0+p)`.  Therefore the derivative of `Psi`
in the `V` direction is onto the real tangent space of `X^N`.  The universal map is a smooth real
submersion.

### 5. Codimension eliminates the uncountable shift parameter

Finite-dimensional parametric transversality gives a residual dense set of `p in V` for which

`Psi_p:U -> X^N`

is transverse to every stratum of `B_(S,z)`.  By (1), a transverse preimage would have negative
dimension; it is empty.  Hence the evaluation matrix has full rank `R` for every `h in U`.

The good perturbations are dense in `V`, so `p` can be chosen arbitrarily small in every prescribed
compact-open neighborhood of zero.  This proves density near every `g_0` in the relative topology
of `E_(A,nu)`.  Avoidance over a compact subset of `U` is open because its evaluation image is
compact and the bad locus is closed.

Exhaust every `Conf_m(C)` by countably many compacts and use finitely many symmetry-separated
patches on each compact.  Finally intersect over the countable collection of `m`, jet orders, and
finite expanded-monomial supports.  The resulting set is comeager in `E_(A,nu)` and eliminates
every differential polynomial relation over `C(z)` for every finite tuple of distinct complex
shifts.

The pure-topology passage of this step — countably many nowhere-dense relation loci in the Baire
constraint space `E_(A,nu)` yield a dense/comeager complement of gauges avoiding all of them — is the
same backbone formalized axiom-clean in `GaloisForLFunctions.BaireGenericAvoidance`
(`dense_setOf_forall_notMem_of_isClosed_interior_empty`), applied here inside the closed real Fréchet
subspace `E_(A,nu)` (itself a Baire space); the analytic input is that each locus is closed with
empty interior via the equivariant codimension count of steps 3–4.

### 6. Divisor, symmetry, and passport

The exponential gauge is zero-free, so `F_g` has exactly the divisor of `W`.  Both factors satisfy
the functional equation and Schwarz reality, hence so does `F_g`.  At `a in A`,

`g(z)=O((z-a)^(nu(a)))`

implies

`exp(g(z))=1+O((z-a)^(nu(a)))`.

Therefore the derivatives of `F_g` and `W` agree through order `nu(a)-1`.  This completes the
proof. `QED`

## Same-passport critical/off-critical pair

The preceding theorem can be made into a literal indistinguishability pair.  Put `w=z-1/2`, choose
real `t!=0` and `a in C` with `Re(a) Im(a)!=0`, and set

`W_crit(z)=(w^2+t^2)^2`,

`W_off(z)=((w^2-a^2)(w^2-conj(a)^2))^2`.

Both are entire, functional-equation invariant, and Schwarz-real.  The divisor of `W_crit` is on
the critical line, whereas every zero of `W_off` is off it.  Both functions are positive away from
their zeros on the fixed sets of the two anti-holomorphic involutions.

Let `A` be any finite `G`-invariant set avoiding both divisors, with any invariant finite jet depth.
The quotient `W_crit/W_off` has compatible local logarithms at `A`: on a point fixed by an
anti-holomorphic involution the quotient is positive, so the real logarithm is available; elsewhere
choose one branch and transport it around the free `G`-orbit.  Equivariant finite Hermite
interpolation gives a symmetric Schwarz-real polynomial `u` whose jets agree with these local
logarithms to the required orders.  Replacing `W_off` by `W_off exp(u)` therefore makes its entire
finite passport at `A` identical to that of `W_crit`, without changing its divisor.

Apply the theorem independently to the two bases.  It produces `F_crit,F_off` which

1. obey the same scalar functional equation and Schwarz reality;
2. have identical prescribed finite jets at every point of `A`;
3. have free full complex translation-differential fields, canonically isomorphic by
   `(T_h F_crit)^(n) |-> (T_h F_off)^(n)`;
4. have opposite critical-line divisor predicates.

Thus no invariant of the abstract full complex differential-translation field, augmented by the
two scalar symmetries and any fixed finite analytic passport, can select the RH-type divisor
predicate.

## Named open core

Closed by the equivariant passport Hermite lemma and real parametric transversality above.

## Exact route consequence

The theorem gives critical-line and off-critical symmetric divisors carrying the same
maximal full-translation differential matroid while also satisfying the scalar functional equation,
Schwarz reality, and any fixed finite normalization passport.  It therefore rules out every route
implementation whose decisive selector uses only those data.

This covers, in particular, proposed implementations of Li, Weil, Hilbert--Polya, Connes,
de Branges, or Nyman--Beurling in which the missing positivity, spectral, or norm selector is claimed
to be forced merely by hypertranscendence plus the scalar symmetries and finitely many normalized
values.  It does **not** refute the complete classical criteria: growth, positivity, Hilbert-space
geometry, Euler normalization, canonical products, and the actual divisor are not preserved by the
isomorphism.

## Attacks and boundaries

1. **The symmetry space is real, not complex.**  The proof uses real parametric transversality.
   Equivariant Hermite interpolation is real-linearly onto arbitrary complex jets at a packet of
   free symmetry-orbit representatives, which supplies the required real submersion.
2. **Fixed axes do not obstruct interpolation.**  Evaluation points are chosen off all fixed axes;
   they are proof probes, not zeros or prescribed normalization points.
3. **The finite passport really is fixed.**  Every perturbation is divisible by the symmetric
   passport polynomial `H`, so no normalization jet is altered.
4. **Finite order is not preserved.**  Generic entire exponential gauges have uncontrolled growth.
   This is the principal boundary between the present no-go and the completed zeta function.
5. **No positivity is preserved.**  The theorem does not retain Weil positivity, a de Branges
   Hermite--Biehler inequality, a Nyman--Beurling norm closure, or a self-adjoint spectral measure.

## Novelty gate

- **Proof gate:** passes.  The only additional issue beyond the unconstrained theorem is equivariant
  jet-surjectivity; the four-orbit Hermite construction and passport multiplier prove it.
- **Significance gate:** provisionally passes.  The law shows that full uncountable
  transformal-differential freeness remains divisor-blind even inside the exact scalar symmetry
  cage and after every fixed finite analytic normalization.
- **Parent-theory gate:** open.  Equivariant Hermite interpolation and parametric transversality are
  classical engines, but their joint fixed-divisor/full-translation consequence was not found in
  the parent theories checked so far.
- **Literature gate:** open.  Exact searches have not located this theorem; a specialist
  MathSciNet/zbMATH and citation-chain audit remains necessary.
- **Rediscovery gate:** open.

No scientific-newness label is applied until all gates pass.

## Parent comparison

1. **Forstneric, 2006, holomorphic jet transversality.**  Theorems 4.2--4.3 prove residual jet
   transversality for holomorphic maps from a Stein source to a flexible target.  This supplies the
   general transversality paradigm, but its mapping space is unrestricted.  It does not state that
   the highly constrained orbit map generated by one entire function avoids every differential
   rank-defect locus for all uncountably many shift configurations, nor does it preserve a divisor,
   the two involutions, or a finite passport.
   Source: `https://arxiv.org/abs/math/0401439`.
2. **Edwards, 1951, independent translates.**  Edwards studies topological linear independence of
   translates in translation-invariant function spaces.  This is an important precursor to
   full-orbit independence, but it is linear/closed-span independence, not differential algebraic
   independence, and it contains no fixed-divisor or symmetry-fiber theorem.
   Source: `https://doi.org/10.5802/aif.35`.
3. **Bès--Conejero--Papathanasiou, 2018, hypercyclic algebras.**  Their genericity concerns dense
   orbits and algebras for convolution/composition operators.  It neither gives simultaneous
   differential independence for every complex shift tuple nor works in a prescribed divisor and
   symmetry fiber.  Source: `https://arxiv.org/abs/1706.08022`.
4. **Rubel, 1992, the DA entire-function ring.**  This identifies the algebraic setting of
   differentially algebraic entire functions, but does not contain the translation-orbit
   genericity or divisor-blindness conclusion.  Source: `https://doi.org/10.2307/2275279`.

These comparisons show that the proof engines are classical while the combined law is not an
immediate quoted theorem.  They do not by themselves establish novelty.

## Lean status

**Complete, unconditional, axiom-clean** (`[propext, Classical.choice, Quot.sound]`).  The capstone
is `GaloisForLFunctions.HTGeometry.symmetryCaged_fullTranslationFreeness_denseResidual` in
`formal/GaloisForLFunctions/HTGeometry/SymmetryCagedTranslationFreeness.lean`; see the assembly
section below for the module chain.

## Gates

- [x] 0 -> 1: exact claim and open core isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] 2 -> 3: complete unconditional claim formalized in Lean
- [ ] independent specialist proof and novelty audit (human gate; not a formalization item)

## Log

- 2026-07-11 -- Proved equivariant passport jet-surjectivity by four-orbit Hermite interpolation
  and a symmetric vanishing multiplier.
- 2026-07-11 -- Re-ran the full-configuration codimension argument over the real symmetry space.
  Functional-equation symmetry, Schwarz reality, arbitrary finite normalization jets, prescribed
  divisor, and maximal full-translation differential freeness coexist.
- 2026-07-11 -- Rebuilt `FiniteHermiteCRT.lean`.  Its two equivariant Hermite theorems use only
  Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.  This verifies the finite
  interpolation anchor only; the complete theorem remains unformalized.

## Lean assembly — the theorem is closed

The route is the one that closed `fixed-divisor-full-complex-translation-freeness`, run inside the
constraint space.  The corpus's own compact-patch codimension calculus
(`expandedEvaluation_compactPatchAvoidance_dense`, together with
`expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional`) already carries
steps 3 and 5 unconditionally and stratification-free, so what this card had to add was the
equivariant half of steps 2 and 4 and the constraint space itself.

**Symmetric polynomials** (`SymmetricPolynomialJets.lean`).  `reflectPoly P = P(1-X)` and
`conjPoly P = P` with conjugated coefficients are the two involutions; `avgPoly` averages over the
group they generate.  `reflectPoly_avgPoly`, `conjPoly_avgPoly` give the two symmetries, and
`iterate_derivative_avgPoly_eval` evaluates every jet of the average as the four-term equivariant
combination.  This is the equivariant passport Hermite lemma of step 2, in the exact form the probe
needs.

**The passport multiplier** (`SymmetricPassportPolynomial.lean`).
`symPassportPoly A dep = ∏_{a∈A} (X - a)^{2·dep a}` is invariant under both involutions when `A` and
`dep` are (`reflectPoly_symPassportPoly`, `conjPoly_symPassportPoly` — the even exponent absorbs the
sign), is nonzero off `A` (`eval_symPassportPoly_ne_zero`), and kills every prescribed jet
(`eval_iterate_derivative_symPassportPoly_mul`, from
`dvd_iterate_derivative`).

**The constrained probe** (`SymmetricGaugeProbe.lean`).  `symProbe` is `symPassportPoly · avgPoly`
applied to a coefficient window; `reflectPoly_symProbe_poly` and `conjPoly_symProbe_poly` say it
stays in the cage.  **`surjective_symProbe_jet`** is the crux: at a node family whose symmetry orbit
`orbitNode` is injective and off the origin and off `A`, the constrained probe still realizes every
jet target.  The proof extends the target equivariantly to the four-point orbit, interpolates there
with the corpus's `windowJetMap` isomorphism, and observes that the four averaged terms then
contribute the same value at the representative; multiplication by the passport polynomial is
inverted by `leibnizJetMatrix`.

**The constraint space** (`SymmetricGaugeSpace.lean`).  `symGaugeSet A dep` is closed in the
compact-open gauge space (`isClosed_symGaugeSet` — each of the two functional identities and each
passport jet is a closed condition, by `continuous_gaugeEval` and `continuous_gaugeJet`), hence
completely metrizable and `BaireSpace`.  `symChart` is the finite-dimensional chart: the probe stays
inside the cage (`probeGaugeChart_mem_symGaugeSet`).

**Free orbits** (`SymmetricRowPacketAtlas.lean`).  Translating a collision-free row packet along the
diagonal `t ↦ t(1+i)` makes every orbit point an affine function of `t` with a nonzero coefficient,
and the four coefficients `1±i, -(1±i)` are pairwise distinct (`orbitCoef_injective`).  So each bad
condition excludes at most one real `t`, apart from the divisor of `W`, which excludes a countable
set.  Since `ℝ` is uncountable a good `t` exists
(`injectiveShiftConfigurations_covered_by_symGoodCombinedRowPackets`), and compactness gives a finite
atlas.

**The assembly** (`SymmetryCagedTranslationFreeness.lean`).

```text
compact_injectiveShiftPatch_has_dense_completeAtlas_symGauge
global_injectiveShifts_symGaugeExpandedFullRankWitness_dense_residual
allFinitePatterns_symGaugeExpandedFullRankWitness_dense_residual
allFinitePatterns_symGaugeExpandedRelationFree_dense_residual
not_familyDifferentiallyAlgebraicOn_symGaugeCarrier_of_relationFree
symmetryCaged_fullTranslationFreeness_denseResidual      -- the theorem
exists_symGauge_fullTranslationFreeness                  -- existence form
iteratedDeriv_gaugeCarrier_eq_of_flat                    -- the passport survives
exists_pair_symmetryCaged_criticalLine_blindness         -- the route consequence
```

The capstone reads: for a nonzero entire `W` with `W(1-z)=W(z)` and `W(conj z)=conj W(z)`, and for
any finite set `A` and jet depths `dep` invariant under the group generated by the two involutions,
the set of constrained gauges `g` for which every finite family of distinct complex translates of
`W·exp(g)` satisfies no algebraic differential relation over the coordinate is **dense and residual**
in the Baire constraint space `symGaugeSet A dep`, and for every such `g` the source `W·exp(g)`

* has exactly the divisor of `W` (`analyticOrderAt` equal at every point);
* satisfies `F(1-z)=F(z)` and `F(conj z)=conj F(z)`;
* has the same jets as `W` through order `dep a − 1` at every `a ∈ A`.

`exists_pair_symmetryCaged_criticalLine_blindness` instantiates this with
`critSymDivisor t = ((z-1/2)² + t²)²` and `offSymDivisor a = ((z-1/2)² − a²)²((z-1/2)² − conj(a)²)²`:
every zero of the first has real part `1/2` (`critSymDivisor_zero_re`) and no zero of the second does
(`offSymDivisor_zero_re`), while both carry symmetric Schwarz-real sources whose full complex
translation orbits are differentially algebraically independent over the coordinate.  So the
critical-line divisor predicate is invisible to the differential-translation structure together with
the two scalar symmetries.

### Exact scope of the formalized pair

`exists_pair_symmetryCaged_criticalLine_blindness` formalizes items 1, 3 and 4 of the
"same-passport" list — the two scalar symmetries, the free full complex translation orbits, and the
opposite critical-line divisor predicates — with the empty passport, for which item 2 ("identical
prescribed finite jets at every point of `A`") is vacuous.  The Statement of the card, which is what
gate `2 -> 3` asks for, is formalized in full including a nonempty invariant passport: for every
`G`-invariant `A` and invariant depths `dep`, every gauge in the residual set keeps the jets of `W`
through order `dep a − 1` at every `a ∈ A` (`iteratedDeriv_gaugeCarrier_eq_of_flat`).

Matching a *nonempty* passport across the two different sources of the pair is a separate
construction: replace `W_off` by `W_off·exp(u)` for a symmetric Schwarz-real polynomial `u`.  Every
ingredient is present — `surjective_symProbe_jet` with the trivial multiplier realizes arbitrary
jets by a symmetric polynomial, `iterate_derivative_reflectPoly` and `iterate_derivative_conjPoly`
transport those jets across the orbit, and the triangular solve needs only the surjectivity of
`expJetMap` onto vectors with nonvanishing head — but the assembly is not written, and no axiom or
placeholder stands in for it.
