# Deterministic level-2 entropy-budget law for the prime-log orbit

- **ID:** `prime-log-level-two-entropy-budget-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / GROWING-DIMENSIONAL ARITHMETIC DYNAMICS / LEVEL-2 LARGE DEVIATIONS
- **Scientific status:** `[ACTIVE FRONTIER CONJECTURE]`
  `[EXACT-OBJECT NOVELTY AUDIT PASSED 2026-07-20]`
  `[SURVIVES HOSTILE PRELIMINARY ATTACK]`
- **Statement:** On every exponential clock with entropy `tau` per prime, the one deterministic
  orbit `(t log p)_(p<=X)` realizes exactly the phase profiles whose conditional relative entropy
  is at most `tau`, and it pays their full independent-Haar entropy with no arithmetic discount.

## Goal

This card asks for one theorem-level conjecture, not a family of scalar estimates.

Let

```text
d_X = pi(X),
E = [0,1] x T,
m_T = normalized Haar measure on T,
```

and define the empirical prime-phase field

```text
L_X(t) = d_X^(-1) sum_(p<=X) delta_(p/X, exp(-i t log p)) in P(E).      (1)
```

The prime number theorem gives

```text
d_X^(-1) sum_(p<=X) delta_(p/X) => Lebesgue measure dv on [0,1].       (2)
```

For `nu in P(E)`, define

```text
H(nu) = integral_[0,1] Ent(nu_v | m_T) dv                            (3)
```

when the first marginal of `nu` is `dv` and `nu = integral nu_v dv`; set `H(nu)=+infinity`
otherwise.  Here `Ent` is Kullback--Leibler relative entropy.

For every sequence `T_X -> infinity` such that

```text
log T_X / d_X -> tau in [0,infinity),                                (4)
```

and every continuous real functional `Phi` on the compact space `P(E)`, conjecture

```text
lim_(X->infinity) d_X^(-1) log [
  T_X^(-1) integral_(T_X)^(2T_X) exp(d_X Phi(L_X(t))) dt
]

= sup_{nu in P(E), H(nu)<=tau} { Phi(nu) - H(nu) }.                  (Q)
```

Equation `(Q)` is the only active conjecture on this card.

Its positive content is an entropy conservation law:

```text
time entropy available             = tau d_X,
cost of a macroscopic phase field  = H(nu) d_X,
accessible fields                  = {nu : H(nu)<=tau}.               (5)
```

The arithmetic assertion is that the logarithms of the primes create no additional exponential
gain or loss.  Unique factorization removes exact resonances; `(Q)` says that the remaining
exponentially fine near-resonances do not renormalize conditional relative entropy.

This is independent of RH.  It contains no zeta zero, Weil positivity, spectral realization, or
zero-free hypothesis.  A proof would solve a concrete frontier problem in deterministic
high-dimensional dynamics and analytic number theory before it is used in any Connes application.

## Why this is stronger than the scalar prime-phasor conjecture

For `0<=alpha<1`, let

```text
w_alpha(v) = (1-alpha) v^(-alpha),
A_alpha(nu) = integral_E w_alpha(v) z dnu(v,z).                     (6)
```

Although `w_alpha` is unbounded at zero when `alpha>0`, the fixed first marginal `dv` makes
`A_alpha` continuous on the finite-entropy fibre: truncate `w_alpha`, use weak continuity for the
bounded part, and bound the tail uniformly by its `L^1(dv)` norm.

For the discrete fields `(1)`, PNT partial summation and regular variation give the required
exponential-equivalence-free deterministic approximation

```text
sum_(p<=X) a_(p,X) z_p
  - d_X^(-1) sum_(p<=X) w_alpha(p/X) z_p -> 0              (6a)
```

uniformly over all phases `|z_p|=1`; the primes `p<=epsilon X` are controlled first by the
integrable `v^(-alpha)` tail and then `epsilon` decreases to zero.

The contraction principle applied to `(Q)` gives the deterministic entropy-censored Varadhan law
for every regularly varying prime weight `(log p)p^(-alpha)L(p)` simultaneously.  Its scalar rate
is

```text
J_alpha(z) = inf { H(nu) : A_alpha(nu)=z },                         (7)
```

and entropy duality gives

```text
sup_nu { <u,A_alpha(nu)> - H(nu) }
  = integral_0^1 log I_0(|u| w_alpha(v)) dv.                         (8)
```

Thus the earlier Bessel rate is a contraction of one source-independent entropy geometry.  The
level-2 law also controls joint observables, spatially varying prime bands, nonlinear mean-field
potentials, and every bounded continuous phase statistic.  No single weighted Dirichlet
polynomial contains this information.

The existing card
`prime-log-kronecker-coherence-capacity-conjecture.md` is therefore retained only as the detailed
scalar contraction and Connes application.  It is not a second active conjecture.

## Internal frontier

- `[CORPUS]` `UniversalPhaseCoherenceMinimax.lean` proves the ambient worst-frequency
  near-coherence clock and its exact half-entropy coefficient.  It does not give a lower clock for
  the arithmetic vector `(log p)`.
- `[CORPUS]` `CCMPrimePoleFiniteCoherence.lean` proves delayed finite-prime recurrence and the
  `tau_X -> infinity` coherence branch.  It does not identify any finite entropy profile.
- `[CORPUS]` `DirichletPolynomialSincEnergy.lean` isolates every finite-time defect in explicit
  off-diagonal sinc-weighted prime-product near-collisions.  It does not determine their
  exponential pressure when the moment depth is comparable to `pi(X)`.
- `[LOCAL-RESEARCH]` `regular-variation-weighted-steinhaus-ldp.md` gives the independent-Haar
  comparison law on paper.  That is parent theory, not the deterministic assertion `(Q)`.
- `[LOCAL-RESEARCH]` `prime-log-kronecker-coherence-capacity-conjecture.md` states the contracted
  phasor law.  Equation `(Q)` explains why all of its regular-variation rate functions should come
  from one conditional-entropy object.
- `[LOCAL-RESEARCH]` `primorial-zero-edge-renewal-process-law.md` isolates the actual Boolean
  zero-edge shell of the resonance problem: after sampling the cutoff in natural density, it asks
  for Poisson statistics, overlap erasure, and independent renewal across consecutive primorials.
  This is a strict prerequisite-scale frontier, not a proof of `(Q)`; every-cutoff control, general
  Fourier alphabets, amplitudes, and signed cluster pressure remain.

The internal residue is exact:

```text
Does the single prime-log orbit reproduce the independent-Haar level-2 entropy
on time intervals of length exp(tau pi(X)), including the hard entropy cutoff?   (9)
```

Nothing already formalized answers `(9)`.

## External frontier

The hostile comparison separates five parent theories.

1. `[LITERATURE]` Sanov and triangular-array large-deviation theory give `(Q)` after replacing
   `exp(-it log p)` by independent Haar phases.  This proves the candidate rate function, not the
   deterministic transference.
2. `[LITERATURE]` Granville--Lamzouri treat large deviations for approximately independent
   arithmetic variables, explicitly including `p^(it)`.  At cutoff `p<=X` and
   `log T asymp pi(X)`, the available product-separation depth is of order
   `pi(X)/log X`, while `(Q)` requires macroscopic Fourier or moment depth of order `pi(X)`.
3. `[LITERATURE]` Guth--Maynard prove major new frequency bounds for large values of general
   Dirichlet polynomials.  Their theorem does not identify the level-2 phase-profile rate, the
   entropy cutoff, or the signed smooth-product pressure at the present depth.
4. `[LITERATURE]` fixed-dimensional integrable-flow hitting laws are generally non-Poisson and are
   described through affine lattices.  Infinite-torus Kronecker theory proves minimality and
   unique ergodicity under algebraic hypotheses.  Neither gives a cofinal dimension/time entropy
   law for the fixed vector of prime logarithms.
5. `[LITERATURE]` local-REM and high-dimensional random-lattice theorems explain how random energy
   landscapes or random lattices can Poissonize.  They average the coefficients or lattice.  The
  prime-log orbit is fixed and deterministic.

Primary comparison sources:

- A. Granville and Y. Lamzouri, *Large deviations of sums of random variables*,
  <https://arxiv.org/abs/2104.02048>.
- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*,
  <https://arxiv.org/abs/2405.20552>.
- C. P. Dettmann, J. Marklof, and A. Strombergsson, *Universal hitting time statistics for
  integrable flows*, <https://arxiv.org/abs/1606.04068>.
- L. Baroni, *Kronecker Flow on the Infinite Torus*, <https://arxiv.org/abs/2604.02213>.
- B. Klartag, *Poisson approximation of random lattices*,
  <https://arxiv.org/abs/2605.10479>.
- C. Borgs, J. Chayes, S. Mertens, and C. Nair, *Proof of the local REM conjecture for number
  partitioning I*, <https://arxiv.org/abs/cond-mat/0501760>.

Exact-object searches on 2026-07-20 found no level-2 Sanov or Varadhan law for a deterministic
growing-dimensional Kronecker orbit, no conditional-relative-entropy law for the empirical
prime-phase field `(1)`, and no theorem that reaches the required signed prime-product pressure.
The audit included title, abstract, statement, and mechanism searches rather than phrase matching.
The conjecture therefore passes the project's exact-object novelty gate.  Historical priority can
still be corrected by an actual matching source, but generic Sanov theory, fixed-dimensional
Kronecker dynamics, random-lattice Poissonization, and shallower prime-phase large deviations are
not matches.

### Exact frontier separation

The conjecture begins strictly after the strongest located parent results.

1. Granville--Lamzouri provide arithmetic large-deviation transference for approximately
   independent families including `p^(it)`, but not the full empirical phase field and not the
   macroscopic Fourier depth `k asymp pi(X)` on clocks `log T asymp pi(X)`.
2. Guth--Maynard control large values of general Dirichlet polynomials and obtain major
   number-theoretic consequences, but do not identify a level-2 rate functional or a hard time-
   entropy accessibility boundary.
3. Dettmann--Marklof--Strombergsson obtain universal but generally non-Poisson hitting laws for
   fixed-dimensional integrable flows through affine-lattice limits.  They do not take the
   simultaneous dimension/rare-target limit for the fixed prime-log direction.
4. Klartag proves exponentially accurate Poisson approximation for random high-dimensional
   lattices in suitable regions.  The randomness is in the lattice; `(Q)` is quenched at the one
   deterministic arithmetic lattice generated by prime logarithms.
5. Baroni proves structural minimality and unique ergodicity results for infinite-torus Kronecker
   flows.  Those results do not give the finite-clock exponential rate needed to exchange growing
   dimension with time.

Thus the missing theorem is not a restatement of any located parent.  It is a new deterministic
transference principle:

```text
independent-Haar conditional entropy
        + one fixed prime-log orbit
        + an exponential but entropy-limited observation clock
        = exact accessible phase-field geometry.                         (A)
```

Any proof of `(A)` creates new scientific knowledge even before the Connes application, because it
settles a presently untreated cofinal regime shared by analytic number theory, deterministic
high-dimensional dynamics, local-REM theory, and quantum recurrence.

## Hostile attack

### Not a known theorem in new notation

The independent model has the same right-hand side, but replacing one deterministic time orbit by
independent samples is exactly the missing theorem.  Fixed-dimensional unique ergodicity first
sends time to infinity and supplies no rate uniform in `d_X`.  Neither parent permits exchanging
the limits at `log T_X asymp d_X`.

### Not an RH equivalence

The phase field `(1)` uses only the primes, their logarithms, and ordinary time averaging.  The
conjecture makes sense for any multiplicatively independent generator sequence with an asymptotic
position law.  RH is neither an assumption nor a formal consequence of `(Q)` alone.

### Not merely the old scalar conjecture with larger notation

The old law sees only one complex number `A_alpha(L_X(t))`.  Two phase fields can have identical
values under every member of one fixed weight family and still differ under band-local or
nonlinear observables.  Equation `(Q)` determines the full macroscopic phase field and contracts
to every regular-variation weight at once.

### Extreme-case checks

- `tau=0`: only the zero-entropy field `dv x m_T` is accessible.  The conjecture predicts
  deterministic dephasing for every fixed continuous phase-field statistic on every subexponential
  clock with `T_X->infinity`.
- finite `tau`: a profile is present exactly when its conditional entropy fits inside the clock.
- `tau->infinity`: the censor disappears and the right side tends to the ordinary independent-Haar
  Sanov variational formula.
- near-perfect coherence: the entropy of an arc of angular width `sqrt(eta)` is
  `(1/2)log(1/eta)+O(1)`, recovering the already proved universal half-entropy coefficient rather
  than contradicting it.
- constant `Phi`: both sides equal that constant.

### Exact falsifiers

The conjecture is false if any one of the following occurs.

1. There are `tau`, `Phi`, and a clock sequence satisfying `(4)` for which the two sides of `(Q)`
   differ.
2. A family of near-relations among products of at most `O(pi(X))` primes contributes a nonzero
   exponential correction to the independent-Haar pressure.
3. A positive-entropy phase field is reached on clocks of strictly smaller entropy, producing an
   arithmetic entropy discount.
4. A field with entropy below `tau` is exponentially suppressed, producing an arithmetic entropy
   surcharge.

The verdict after the present attack is `SURVIVES PRELIMINARY ATTACK`.  This is not evidence that
`(Q)` is true.

## Exact open core

`[OPEN CORE]` Prove the entropy-censored Fourier-resonance pressure law for every real smooth
one-site potential, uniformly for all linear combinations in each finite test family, and obtain
the exposed-point lower bounds needed for the corresponding finite-dimensional LDP.

The first claim that would count as frontier progress is not the full conjecture and not an
independent-model calculation.  It is the following signed one-potential pressure theorem.

```text
For every real smooth f on [0,1] x T and every tau>=0, the exact signed sum
in (15), at T_X with log T_X/pi(X)->tau, has exponential rate (16).       (P1)
```

`(P1)` is strong enough to see the cancellation between exponentially many near prime-product
relations.  A diagonal moment estimate, an absolute-value majorant, fixed Fourier degree, or a
random-coefficient local-REM theorem does not imply it.  Conversely, `(P1)` jointly for every
finite linear family of smooth potentials, plus the exposed-point lower bound, yields `(Q)` by
finite-dimensional projection and density.  This makes `(P1)` the first honest proof target.

For a real smooth function `f(v,z)` on `E`, the linear functional

```text
Phi_f(nu) = integral_E f dnu                                      (10)
```

turns the left side of `(Q)` into

```text
T_X^(-1) integral_(T_X)^(2T_X)
  product_(p<=X) exp(f(p/X, p^(-it))) dt.                         (11)
```

Fourier expansion of each factor expresses `(11)` as a signed sum indexed by integer exponent
vectors `k=(k_p)` with frequency

```text
Omega_X(k) = sum_(p<=X) k_p log p
            = log product_(p<=X) p^(k_p).                         (12)
```

Unique factorization says `Omega_X(k)=0` only for `k=0`.  The kernel is unsuppressed on the
nonzero vectors with

```text
|Omega_X(k)| <= exp(-tau pi(X))                                  (13)
```

The unsolved assertion concerns the aggregate signed pressure of this core together with the
kernel-damped complement.  It must reproduce exactly the entropy truncation on the right side of
`(Q)`.  Absolute-value bounds are not enough: below the independent saddle the near-resonances must
reproduce the censored free energy, while above it their connected pressure must vanish.

More explicitly, put

```text
g_(p,X)(theta) = exp(f(p/X, exp(i theta))),
gHat_(p,X)(k) = integral_T g_(p,X)(theta) exp(-i k theta) dm_T(theta),
K_T(omega) = T^(-1) integral_T^(2T) exp(-i t omega) dt.             (14)
```

Smoothness gives an absolutely convergent product Fourier expansion, and `(11)` is exactly

```text
sum_(k in Z^(primes<=X))
  [product_(p<=X) gHat_(p,X)(k_p)] K_(T_X)(Omega_X(k)).             (15)
```

The `k=0` term is the independent-Haar product.  The desired linear-potential face of `(Q)` is the
precise signed-pressure identity

```text
lim d_X^(-1) log (the positive real quantity in (15))
 = sup_{H(nu)<=tau} { integral_E f dnu - H(nu) }.                   (16)
```

Thus the open problem is not to bound each near-relation separately.  It is to identify the total
signed pressure of all exponentially fine rational prime-product resonances.  Replacing `(15)` by
the sum of absolute values generally destroys the conjectured censored phase transition.

The algebra generated by functionals `nu |-> integral f dnu` separates points of `P(E)`.  Hence a
joint finite-dimensional LDP for every finite test family, including the lower bound at the
entropy boundary, extends through the Stone--Weierstrass cylinder algebra; exponential tightness
is automatic because `P(E)` is compact.  This would yield `(Q)` for every continuous `Phi`.  The
first genuinely arithmetic lemma is therefore the aggregate signed pressure of the near-relations
`(13)`, not the independent Sanov theorem.

## Research programme

1. Prove the independent triangular-array level-2 law and the contraction identity `(8)` as
   parent-theory infrastructure; do not count it as novelty.
2. Reduce smooth linear potentials to the signed resonance pressure `(11)`--`(13)` with uniform
   Fourier-tail control.
3. Establish the signed prime-product local limit `(15)`--`(16)` at exponential resolution by
   separating diagonal, isolated near-resonance, and connected cluster pressures.
4. Prove that connected clusters contribute no extra exponential entropy, or use the first
   surviving cluster to falsify `(Q)` and replace the rate functional.
5. Only after the paper proof closes, formalize the exact theorem.  No Lean infrastructure is
   justified while `[OPEN CORE]` remains.

## Gates

- [x] 0 -> 1 in-progress: exact level-2 object and rate function defined
- [x] internal corpus frontier audited
- [x] exact-object external novelty audit completed through 2026-07-20
- [x] scalar regular-variation law identified as a strict contraction
- [x] hostile falsity, circularity, rediscovery, and significance attacks recorded
- [ ] prove the smooth-cylinder signed resonance pressure law
- [ ] deduce the full level-2 Laplace principle
- [ ] complete citation ancestry and descendancy audit after a proof exists
- [ ] 1 -> 2 fully-proven: complete dependency-closed paper proof
- [ ] 2 -> 3 formalized: exact unconditional Lean theorem and axiom audit

## Log

- 2026-07-20 -- Promoted to the active frontier conjecture after a second exact-object audit against
  the current arithmetic-large-deviation, Dirichlet-polynomial, integrable-flow, infinite-torus,
  random-lattice, and local-REM frontiers.  No located theorem joins a fixed prime-log orbit,
  growing dimension, exponential clock entropy, and the full conditional-relative-entropy phase
  field.  Isolated `(P1)` as the first result that counts as genuine progress; fixed-degree,
  independent-phase, absolute-value, and random-model substitutes explicitly fail the gate.
- 2026-07-20 -- Created after the scalar prime-phasor conjecture survived its exact-object audit
  but failed the strongest-form test: it did not expose the full empirical phase field shared by
  all prime weights.  Conditional relative entropy supplies one candidate geometry, and the
  finite clock supplies a hard entropy budget.  Hostile comparison found the independent Sanov
  law, fixed-dimensional Kronecker dynamics, arithmetic approximate-independence, general
  Dirichlet-polynomial large values, integrable-flow hitting laws, local REM, and random-lattice
  Poissonization, but no deterministic prime-log level-2 theorem.  Verdict:
  `[CONJECTURE] [NOVELTY UNVERIFIED] [SURVIVES PRELIMINARY ATTACK]`; exact open core `(13)`.
