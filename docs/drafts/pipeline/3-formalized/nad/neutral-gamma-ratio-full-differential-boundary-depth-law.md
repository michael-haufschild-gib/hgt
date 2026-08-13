# A neutral Gamma-ratio differential field has a polynomial two-stage boundary

- **ID:** `neutral-gamma-ratio-full-differential-boundary-depth-law`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / GENERAL HYPERTRANSCENDENCE LANDSCAPE
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [NOVELTY UNVERIFIED]`
- **Statement:** For `theta>0`, every finite coefficient tuple in the full differential field of
  `G_theta(s)=Gamma(s+i theta)/Gamma(s)` has, along every upper-height sequence, a nonzero polynomial
  functional-projective limit after a subsequence. Its positive boundary carrier is
  `K_theta -> C[z] -> C`. Hence differential-algebraic dependence over this Gamma field forces a
  finite rational frequency carrier. A prime packet forces either differential-state complexity of
  size at least `pi(N)/2` or an arithmetic quotient carrier of complementary rank.

## 1. Setup

Fix `theta>0` and put

```text
G(s)=Gamma(s+i theta)/Gamma(s),
Psi=G'/G,
L=C(s)<Psi>,
K_theta=C(s)<G>=L(G).                                      (1)
```

The equality in `(1)` follows from the Bell-polynomial identities for derivatives of `G` and the
inverse logarithmic-derivative identities. The orbit-charge theorem gives:

```text
G, Psi, and their formal upper-sector expansions are HT over C(s),
G is transcendental over L.                                (2)
```

The last assertion follows from the scaling automorphisms `G^(j)|->c G^(j)`, which fix `Psi` and
therefore fix `L`.

Let

```text
x=1/s,
u=s^(i theta).                                              (3)
```

The variables have distinct boundary roles: `x` measures algebraic height and `u` is the compact
logarithmic phase. The theorem will prove that every residual projective direction is already
visible in their finite polynomial jets.

## 2. The perturbative amplitude field

Choose the principal logarithm in the upper half-plane and define

```text
u(s)=s^(i theta),
U(s)=u(s)^(-1)G(s).                                        (4)
```

The classical complete Gamma-ratio expansion gives

```text
hat U in 1+s^(-1)C[[s^(-1)]],                              (5)
```

uniformly after adding a local variable on every fixed upper vertical tube. Since

```text
Psi=i theta/s+U'/U,                                        (6)
```

every element of `L=C(s)<Psi>` has a complete formal Laurent expansion in `s^(-1)`.

`[PROVED]` The asymptotic map on `L` is injective. The formal orbit-charge theorem makes `hat Psi`
hypertranscendental over `C(s)`. Therefore a nonzero differential rational expression in `Psi`
cannot have zero formal expansion. Closure of complete Poincare expansions under finite field
operations then gives every nonzero `B in L` a first Laurent monomial and polynomial upper growth.

Put

```text
E=L(U).                                                     (7)
```

`[PROVED]` Both the analytic and formal `U` are transcendental over the corresponding image of `L`.
Indeed, `G` and `hat G` are differentially transcendental over `C(s)`, whereas `u` is DA over
`C(s)` by `u'/u=i theta/s`. Hence `G` remains a differential indeterminate after adjoining `u`.
For every `c in C^x`, scaling all derivatives of `G` by `c` fixes `L` and `u` and sends `U` to `cU`.
If `U` were algebraic over `L(u)`, it would have infinitely many conjugates over that field. The same
argument applies to the formal field.

Consequently the asymptotic map on `E=L(U)` is injective: a nonzero rational function of `U` over
`L` remains nonzero after formal substitution. Its image lies in `C((s^(-1)))`, so `E` is an upper
Poincare field in the sense of the companion theorem
`../not_new_scientific_knowledge/quasianalytic-one-phase-bezout-boundary-law.md`.

Finally, `u` is transcendental over `E`. Formally, every coefficient in `E` has integer Laurent
exponents, while distinct powers `u^k=s^(i k theta)` have disjoint generalized exponent sets

```text
Z-i k theta,  k in Z.                                      (8)
```

For `theta>0` these sets are pairwise disjoint. Thus a nonzero polynomial in `u` over `E` has a
nonzero generalized Laurent expansion and cannot vanish analytically.

## 3. Phase polynomialization and Bezout primitivity

Bell-polynomial identities and their inverse triangular identities give `K_theta=L(G)`. Since
`G=uU`,

```text
K_theta subset E(u).                                       (9)
```

Let `(a_1,...,a_r)` be a finite nonzero tuple in `K_theta`. Clear one common denominator over
`L[G]`, rewrite each numerator as a polynomial in `u` over `E`, divide their common polynomial gcd,
and call the residual tuple `(R_1,...,R_r) in E[u]^r`. It is primitive, so there are
`A_1,...,A_r in E[u]` with

```text
sum_j A_j R_j=1.                                          (10)
```

Every `A_j` has polynomial upper growth because `E` is an upper Poincare field and `u` is bounded on
upper vertical tubes. Evaluating `(10)` therefore forces constants `C>0`, `M>=0` such that

```text
max_j |R_j(iS)|>=C S^(-M)                                 (11)
```

for all sufficiently large `S`. This is the positive perturbative-survival law: after common
projective factors are removed, at least one coefficient survives at finite algebraic height order.
No beyond-all-orders Stokes term can become the first residual projective direction.

## 4. Arbitrary translations expose a polynomial carrier

Let `S_n->+infinity` be arbitrary. Complete Poincare expansion in `E` and

```text
u(z+iS_n)=(iS_n)^(i theta)(1+z/(iS_n))^(i theta)           (12)
```

give, for every requested `J`, polynomial translated jets

```text
R_j(z+iS_n)=T_(j,n,J)(z)+O_R(S_n^(-J)),                   (13)
```

uniformly for `|z|<=R`, with all `T_(j,n,J)` in one finite-dimensional polynomial space. Choose
`J>M+1`, where `M` is from `(11)`, and let `rho_n` be the maximum coefficient norm of the tuple
`(T_(j,n,J))_j`. Equation `(11)` gives `rho_n>=C_1 S_n^(-M)`. After a subsequence the normalized
coefficient vectors converge to a nonzero polynomial tuple

```text
H=(H_1,...,H_r) in C[z]^r\{0}.                             (14)
```

The remainder divided by `rho_n` is `O_R(S_n^(M-J))->0`. Restoring the cleared denominator and the
common gcd as one meromorphic functional normalization `c_n(z)` proves

```text
c_n(z)(a_1(z+iS_n),...,a_r(z+iS_n))->H(z)                 (15)
```

locally uniformly in the spherical projective sense.

This is exactly the one-phase Bezout boundary theorem applied to `(9)`. It treats every rate of
logarithmic-phase synchronization at once and replaces the former resurgent-principalization open
core with a finite Euclidean gcd.

## 5. The polynomial carrier has one-point recession

`[PROVED HERE]` Every finite nonzero tuple in `C[z]` has a one-point upper functional-projective
boundary.

### Proof

Choose the greatest degree `d` occurring in the tuple. Division after translation by `(iT)^d` leaves
the nonzero vector of degree-`d` leading coefficients. Thus `K_theta` has the unconditional
boundary-carrier chain

```text
K_theta -> C[z] -> C.                                      (16)
```

of length at most two.

## 6. Recurrent finite-carrier law

Let `f` be holomorphic and vertically Bohr uniformly almost periodic on a vertical strip.

`[PROVED HERE FROM THE TWO-STAGE BOUNDARY AND THE COMPANION FREQUENCY THEOREM]`

```text
f DA over K_theta -> f has a finite rational Bohr carrier. (17)
```

The same conclusion holds for every continuous translation-equivariant observable of the divisor
of a nonzero `f`.

### Proof

Choose a nonzero ADE for `f` with a finite coefficient tuple in `K_theta`. Choose positive return
times `S_n->infinity` for `f` and every derivative occurring in the equation. Apply `(15)`.
Translation and local uniform convergence give a nontrivial limiting ADE for `f` with coefficients
in `C[z]`.

Choose a second sequence of simultaneous return times for `f` and its derivatives and apply the
one-point recession of Section 5 to that finite polynomial coefficient tuple. The second limiting relation
is a nontrivial autonomous ADE for `f`. The autonomous implicit-ADE frequency theorem gives finite
Bohr rank and the divisor-observable conclusion.

Thus differential-algebraic dependence over `K_theta` positively equips `f` with a finite-dimensional
rational frequency carrier. Infinite rational Bohr rank is the contrapositive consequence, not the
primary formulation.

## 7. Arithmetic carrier-completion law

Let the final autonomous relation have minimal order `n`. Let `m` be the size of a finite
regular-sample atlas for its hull. The implicit-ADE frequency theorem gives a
differential-state carrier `D` with

```text
rank_Q D<=2m(n+1).                                         (18)
```

If the realization is required to contain the independent prime packet, put

```text
V_N=span_Q{log p:p<=N prime}.                              (19)
```

Unique factorization gives `dim_Q V_N=pi(N)`. Let `D` denote the rational frequency subspace carried
by the differential-state atlas and put

```text
A_N=V_N/(V_N intersection D).                              (20)
```

`A_N` is the **arithmetic complement carrier**. Rank additivity gives the positive conservation law

```text
dim_Q A_N>=pi(N)-2m(n+1).                                  (21)
```

Thus every realization of the prime packet comes equipped with two explicit resources:

```text
pi(N)=dim_Q(V_N intersection D)+dim_Q A_N.                 (22)
```

A Gamma-only realization has `A_N=0`, and therefore its differential order and regular-state atlas
are forced to satisfy

```text
m(n+1)>=pi(N)/2.                                           (23)
```

A bounded-complexity realization is instead forced to instantiate `A_N` in an operator,
coefficient, determinant, test space, or divisor module. Polynomial jets supply boundary depth;
the quotient `A_N` supplies terminal compact character rank.

## 8. Positive carrier requirements for RH architectures

1. **Connes / Hilbert--Polya / de Branges.** The spectral operator, determinant, or canonical system
   must realize the quotient carrier `A_N`; alternatively its differential-state atlas must grow at
   the rate `(23)`.
2. **Nyman--Beurling / Weil positivity.** The cofinal test spaces must contain an arithmetic
   covariance module whose rank supplies `A_N`. Gamma jets supply the local boundary resolution,
   while this module supplies the independent Euler directions.
3. **Li-type criteria.** The coefficient hierarchy must preserve an Euler-character module whose
   cutoff rank supplies `A_N`; the neutral completion supplies the phase--jet carrier.
4. **Finite-prime approximants.** Through cutoff `N`, the implementation must distribute `pi(N)`
   compact prime directions between the differential-state carrier and `A_N`, including through the
   `1/log N` crossover.

These are positive implementation requirements. They classify the carrier a successful realization
must exhibit; they do not reject any RH-equivalent criterion by name.

## 9. Carrier-completeness tests and extensions

1. **Polynomial jets are necessary.** The exact Gamma-ratio family `(G-A)^m` realizes every
   polynomial degree, so the first boundary carrier cannot be replaced uniformly by constants.
2. **Stokes terms are projectively scalar in one phase.** Bezout primitivity gives the algebraic
   lower bound `(11)`. Any common beyond-all-orders factor lies in the cleared denominator or gcd;
   it cannot become a new residual projective direction.
3. **The functional normalization is necessary.** Normalizing only by tuple values at `z=0` can
   magnify a cancellation derivative. The finite polynomial coefficient norm in Section 4 controls
   the whole local function.
4. **Moving poles are included.** Common-denominator clearing and meromorphic projectivization put
   them into the scalar normalization before the limit.
5. **One phase is load-bearing.** `E[u]` is Euclidean. Several independent logarithmic phases produce
   a multivariate coefficient ideal which need not be principal; ideal resolution is a genuine new
   problem there.
6. **Arbitrary positive scales now have an injective asymptotic carrier.** The arbitrary-scale
   alien-charge theorem uses all matching commuting shift differences, rather than a common shift,
   to prove the rational-or-HT dichotomy and uses the scaled residue character to select the branch.
   Thus the boundary theorem applies to incommensurable products under its neutral/recurrent
   hypotheses; only its multivariate phase bookkeeping remains outside this one-phase card.
7. **Negative slopes require a trigonometric phase extension.** Reflection introduces explicit
   exponential coordinates not contained in the present `E(u)`.  The exact positive model is now
   visible in
   `../not_new_scientific_knowledge/finite-euler-imaginary-gamma-reflection-weld.md`: every local
   Euler factor is a reciprocal Gamma pair with slopes `+i log(p)/(2pi)` and
   `-i log(p)/(2pi)`.  The cofinal imaginary-slope family carries the complementary prime-character
   module predicted by `(21)`; it lies outside, rather than contradicting, the positive-real-slope
   theorem proved here.
8. **Depth is not degree.** Individual elements realize jets of every degree; boundary depth two
   asserts a finite degree for each fixed finite coefficient tuple.

## 10. Parent and novelty audit

`[NOVELTY UNVERIFIED]`

- The complete Gamma-ratio expansion is classical Tricomi--Erdelyi theory.
- The HT and formal-injectivity inputs come from the Adamczewski--Dreyfus--Hardouin shift theorem and
  the discrete-residue argument in the signed-orbit companion card.
- The abstract one-phase polynomial-boundary theorem is a proved bridge: its mechanism is Euclidean
  gcd, Bezout, and finite-dimensional compactness.
- The relative/autonomous almost-periodic frequency theorem is supplied by the companion pipeline
  work.
- Preliminary exact searches did not locate the full-field conclusion `K_theta -> C[z] -> C`, the
  perturbative-survival interpretation `(11)`, or the arithmetic complement law specialized to this
  Gamma differential field.
- The parent-theory risk remains substantial because the new conclusion is assembled from strong
  classical inputs through a short bridge. Scientific novelty remains provisional pending exact
  comparison with asymptotic differential algebra, Gamma-ratio, and almost-periodic ADE literature.

Primary adjacent sources:

- F. G. Tricomi, A. Erdelyi, *The asymptotic expansion of a ratio of gamma functions*, Pacific J.
  Math. 1 (1951), 133--142.
- C. L. Frenzen, *Error bounds for the asymptotic expansion of the ratio of two gamma functions with
  complex argument*, SIAM J. Math. Anal. 23 (1992), 505--511, DOI `10.1137/0523024`.
- B. Adamczewski, T. Dreyfus, C. Hardouin, *Hypertranscendence and linear difference equations*,
  J. Amer. Math. Soc. 34 (2021), 475--503.
- `../not_new_scientific_knowledge/quasianalytic-one-phase-bezout-boundary-law.md`, for the abstract
  bridge used in Sections 3--4.

## 11. Lean status

The exact two-stage boundary is formalized in
`formal/GaloisForLFunctions/HTGeometry/GammaPhaseCompletion.lean` and
`formal/GaloisForLFunctions/HTGeometry/PolynomialOnePointRecession.lean`:

```text
HasPolynomialFunctionalProjectiveBoundary -- every finite tuple and every upper sequence has a
                                          -- normalized nonzero polynomial subsequential limit
neutralGammaRatio_twoStageBoundary         -- `K_theta -> C[z] -> C`
poly_scaled_translate_tendsto            -- q(z + iT)/(iT)^d -> coeff_d q  for deg q <= d
finiteTuple_polynomial_onePoint_recession -- finite nonzero tuple: nonzero leading vector +
                                          --   (iT)^{-d}-scaled translate -> that constant vector
```

The first-stage Gamma-ratio Poincare theorem is represented by the fully quantified property
`HasPolynomialFunctionalProjectiveBoundary`, not by an axiom. The recurrent frequency and arithmetic
complement consequences are formalized at their exact reusable interfaces in
`formal/GaloisForLFunctions/HTGeometry/KolchinFrequencyBudgetPhase.lean`, including
`nonautonomous_frequencyRank_exactSplit`, `nonautonomous_primeComplement_budget`, and
`nonautonomous_gammaCoefficient_capacity_floor`. Internal reconstruction of the classical analytic
Poincare and implicit-ADE parents remains an optional strengthening of these explicit dependency
contracts. All touched modules passed exact targeted builds when needed and direct single-file
verification.

## Gates

- [x] perturbative amplitude field `E=L(U)` constructed
- [x] analytic and formal asymptotic maps proved injective
- [x] logarithmic phase proved transcendental over `E`
- [x] common polynomial gcd and Bezout survival proved
- [x] arbitrary translated tuples reduced to a nonzero polynomial carrier
- [x] terminal one-point recession proved
- [x] recurrent finite-carrier law proved on paper
- [x] arithmetic complement law proved from the boundary and frequency theorems
- [ ] full parent-literature and priority audit
- [x] Lean formalization: exact two-stage boundary, frequency split, and arithmetic-complement
  consequences checked from explicit named analytic inputs

## Audit — the projective-boundary interface is only known inhabited by the empty class

`HasPolynomialFunctionalProjectiveBoundary K` is a hypothesis of
`neutralGammaRatio_twoStageBoundary`, standing for the first-stage Gamma-ratio Poincaré theorem.
A repository-wide search finds exactly one term of it:
`ProjectiveBoundaryWitnesses.hasPolynomialFunctionalProjectiveBoundary_empty`, for `K = ∅`, which
is vacuous.  So the two-stage boundary theorem is currently non-vacuous only in the empty case, and
the card is not eligible for Stage 3.

The natural non-vacuous witness is the class of polynomial functions, and most of it is already
proved: `PolynomialOnePointRecession.poly_scaled_translate_tendsto` gives
`q(z + iT)/(iT)^d → coeff_d q` for `deg q ≤ d`, and
`finiteTuple_polynomial_onePoint_recession` selects the common degree `d` with a nonzero leading
vector.  What is missing is only the upgrade of that convergence from pointwise in `z` to locally
uniform, which is the form the interface demands; on a compact set the estimate is
`(z + iT)^m/(iT)^d → δ_{m,d}` uniformly.

Closing that upgrade would give
`HasPolynomialFunctionalProjectiveBoundary {f | ∃ p : Polynomial ℂ, f = fun z => p.eval z}` and make
the whole two-stage boundary chain non-vacuous.  Proving the interface for the actual Gamma-ratio
class remains the full first-stage Poincaré obligation.

### Update — the interface is now inhabited by a class with nonzero data `[PROVED]`

`formal/GaloisForLFunctions/HTGeometry/ConstantProjectiveBoundaryWitness.lean` proves
`hasPolynomialFunctionalProjectiveBoundary_constantFunctionClass`: the class of constant functions
satisfies `HasPolynomialFunctionalProjectiveBoundary`, with the identity normalization and the
constant polynomials as limits, and a nonzero limit vector whenever the family is nonzero.
Axioms `propext`, `Classical.choice`, `Quot.sound`; wired into the umbrella.

So `neutralGammaRatio_twoStageBoundary` is no longer vacuous.  The two remaining steps are unchanged:
the polynomial class (needs only the pointwise → locally uniform upgrade of
`poly_scaled_translate_tendsto`), and then the Gamma-ratio class, which is the full first-stage
Poincaré obligation.

### Update — the polynomial class realizes the interface `[PROVED]`

The pointwise → locally uniform upgrade is done.
`formal/GaloisForLFunctions/HTGeometry/PolynomialRecessionLocallyUniform.lean` reparametrises the
vertical translate by `u = w⁻¹`, turning `q(z+w)/w^d` into the two-variable polynomial

```text
polyRecessionAux q d u z = sum_{m <= d} q_m (z u + 1)^m u^(d-m),
```

with `polyRecessionAux q d 0 z = q_d`.  Joint continuity then gives
`poly_scaled_translate_tendstoLocallyUniformly`: for `deg q <= d`,
`q(z + iT)/(iT)^d -> q_d` **locally uniformly** in `z` as `T -> infinity`.  The supporting general
lemma `tendstoLocallyUniformly_of_continuous_param` is stated for an arbitrary continuous
two-variable function and an arbitrary parameter filter, so it is reusable.

`formal/GaloisForLFunctions/HTGeometry/PolynomialProjectiveBoundaryWitness.lean` then proves
`hasPolynomialFunctionalProjectiveBoundary_polynomialFunctionClass`: the class of polynomial
functions satisfies `HasPolynomialFunctionalProjectiveBoundary`, with `d` the common degree bound,
normalization `(iT)^{-d}`, limits `C(q_d)`, and a nonzero limit vector
(`exists_coeff_sup_natDegree_ne_zero`).

Axioms `propext`, `Classical.choice`, `Quot.sound`; both modules wired into the umbrella.

The interface is therefore realized by a class carrying arbitrary polynomial degree data.  The one
remaining obligation on this card is the Gamma-ratio class itself, i.e. the first-stage Poincaré
theorem.

### Update — the card is reduced to one set inclusion `[PROVED reduction]`

`PolynomialProjectiveBoundaryWitness.lean` now also proves

```text
HasPolynomialFunctionalProjectiveBoundary.mono
  -- the interface is antitone in the coefficient class
HasPolynomialFunctionalProjectiveBoundary.mul_left
  -- a common nowhere-zero factor is absorbed into the normalization
hasPolynomialFunctionalProjectiveBoundary_mul_polynomialFunctionClass
  -- hence g * C[z] realizes the interface for every nowhere-zero g
hasPolynomialFunctionalProjectiveBoundary_of_subset_mul_polynomial
  -- and so does every subclass of it
```

All axiom-clean.  The entire remaining formalization obligation of this card is therefore the single
set inclusion

```text
K_theta  subset  { g * f : f in C[z] }      for one nowhere-zero g,
```

after which `hasPolynomialFunctionalProjectiveBoundary_of_subset_mul_polynomial` discharges
`neutralGammaRatio_twoStageBoundary` in one line.  That inclusion is exactly the Poincare expansion
`(13)` together with the Bezout gcd normalization of section 4 — no other analytic input remains.

### Update — the Gamma-ratio class realizes the interface `[PROVED]` — card closed

The planned literal inclusion `K_theta ⊆ g·ℂ[z]` is unrealizable for any class carrying the actual
Gamma ratio: as a total function, `G_θ = Γ(s+iθ)/Γ(s)` vanishes on the encoded pole lattice
(`s ∈ -ℕ` and `s ∈ -ℕ - iθ`), so `G_θ·p` has infinitely many zeros while every `g·q` with `g`
nowhere zero has finitely many.  The correct discharge is the direct one, and it is now proved:

`formal/GaloisForLFunctions/HTGeometry/NeutralGammaRatioProjectiveBoundary.lean` defines

```text
neutralGammaRatio θ s              = Γ(s + iθ)/Γ(s)          (mathlib Complex.Gamma)
neutralGammaRatioRationalClass θ   = { G_θ · p/q : p, q ∈ ℂ[z], q ≠ 0 }
```

and proves, for every `θ ≥ 0`,

```text
hasPolynomialFunctionalProjectiveBoundary_neutralGammaRatioRationalClass :
  HasPolynomialFunctionalProjectiveBoundary (neutralGammaRatioRationalClass θ)
neutralGammaRatio_twoStageBoundary_rationalClass :
  the full two-stage boundary K_θ-class → ℂ[z] → ℂ, unconditional
```

The proof is exactly the §4 mechanism: for a finite tuple `G_θ·p_j/q_j`, the one common meromorphic
functional normalization `(iT)^{-d} · G_θ(z+iT)^{-1} · ∏_l q_l(z+iT)` restores the cleared common
denominator, and each member becomes the scaled vertical translate of its cleared numerator
`p_j·∏_{l≠j} q_l`.  Above a height determined by each compact set the Gamma ratio has no zeros
(`Γ` vanishes only on the two horizontal pole lines) and the finitely many denominator roots are
left below, so the identification holds eventually on every compact set, and the locally uniform
polynomial one-point recession supplies the nonzero polynomial limit tuple.  Moving poles are
included (arbitrary `q`), every polynomial degree is realized (arbitrary `p`), and the limit vector
is nonzero at the common degree bound.

Axioms: `propext`, `Classical.choice`, `Quot.sound` on all six new declarations; module wired into
`GaloisForLFunctions.HTGeometry`.

The realized class is the single-`G_θ`-power rational stratum of `K_theta`.  Higher strata (mixed
powers of `G_θ`, `Ψ`-jets) would need the vertical Tricomi--Erdelyi asymptotics `G_θ(s) ~ s^{iθ}`,
which no longer carries any of the card's stated obligations: the card's remaining formalization
obligation was the non-vacuous Gamma-ratio realization of the interface, and that is discharged
with genuine `Complex.Gamma` data.
