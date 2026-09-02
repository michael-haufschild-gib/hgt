# Integral Witt ghosts force an infinite completion tail

- **ID:** `ULF-IWG-1`
- **Stage:** 3-formalized
- **Type:** unconditional algebraic/analytic theorem; completion-law survivor
- **Lean:** `GaloisForLFunctions.RHTower.IntegralWittGhostInfiniteTail`; verified

## 1. Big-picture interpretation

Completion cannot isolate a nonzero vacuum by cancelling every higher cyclotomic mode inside an
integral determinant theory. Rational Möbius inversion performs that cancellation uniquely, but
produces a zero-free exponential and uses fractional Euler multiplicities. Integral multiplicity
instead forces every nonzero ghost to propagate through infinitely many prime-power degrees.

Thus the source of the required noncompactness is not merely infinitely many primes. It is the
failure of rational ghost polarization to descend to the integral divisor lattice. The missing
global counterchannel must retain an all-depth integral interaction tail; no finite jet, finite
ghost profile, or scalar cubic current can be the completed torsion.

## 2. Corpus and literature audit

Corpus search used `scripts/formal_tools.py research` for big-Witt ghosts, Möbius inversion,
cyclotomic completion, integral descent, cross-prime compensation, and determinant torsion.

- `DeningerBigWittGhost` proves the integral Euler-coordinate ghost formula
  `g_m = sum_(d|m) d c_d` and canonical completed big-Witt multiplication.
- `DeningerBigWittFrobeniusCrossPairCoherentCompensator` constructs a genuine nonlocal
  cross-prime compensator, but proves cancellation only at the transgressed first/second ghost.
- `FrankensteinBigWittIntegralBidirectionalGammaDescent` shows integral bidirectional lifting
  detects neutral horizontal grade, but source production of that lift is open.
- `cofinal-cyclotomic-torsion-collapse-and-counterdivisor-law.md` proves that cofinally preserved
  residue-cell torsions force a zero entire limit unless a negative counterdivisor is generated.
- `SourceHorizontalHolomorphic*NoGo` excludes scalar holomorphic unitizations as Xi completion.

External parents, checked as primary sources:

- Moree, *The formal series Witt transform*, arXiv:math/0311194: Möbius/necklace inversion and
  cyclotomic Euler products.
- Cuntz--Deninger, *An alternative to Witt vectors*, arXiv:1311.2774: Witt rings as completions of
  monoid rings.
- Bal, *Dold--Gauss Congruences, Norm Descent, and Rational Rigidity*, arXiv:2509.25038: integral
  ghost image, localized denominators, and rigidity of algebraic/cyclotomic Euler products.
- Campbell et al., *K-Theory of Endomorphisms, the TR-Trace, and Zeta Functions* (2025):
  characteristic determinants as Witt/TR classes retaining all iterate traces.

The abstract Witt and Dold facts are known. New leverage here is their exact fusion with the
corpus's cofinal cyclotomic-collapse theorem: the required counterdivisor cannot be finite-depth
or a rational diagonal cancellation.

## 3. The integral completion-tail theorem

Let `c_n in Z` for `n >= 1`, and define its ghost sequence

`g_m = sum_(d|m) d c_d`.

Equivalently, for the formal Euler product

`F(z) = product_(n>=1) (1-z^n)^(c_n)`,

one has

`-z F'(z)/F(z) = sum_(m>=1) g_m z^m`.

### Theorem IWG-1 (prime-extension congruence)

For every prime `p` with `p` not dividing `m`,

`g_(mp) = g_m mod p`.

#### Proof

Divisors of `mp` split uniquely into `d` and `pd` with `d|m`. Hence

`g_(mp) = sum_(d|m) d c_d + p sum_(d|m) d c_(pd)`,

which is congruent to `g_m` modulo `p`. QED.

### Theorem IWG-2 (no nonzero finite integral ghost)

If `{m : g_m != 0}` is finite, then every `g_m` and every `c_n` is zero.

#### Proof

Fix `m`. Choose a prime `p` larger than the ghost-support bound, larger than `|g_m|`, and not
dividing `m`. Then `g_(mp)=0`. IWG-1 gives `p | g_m`; since `p>|g_m|`, `g_m=0`. This holds for
every `m`. Finally

`g_n = n c_n + sum_(d|n, d<n) d c_d`

and induction on `n` gives `c_n=0` for every `n`. QED.

### Corollary IWG-3 (a vacuum forces an infinite prime tail)

If `g_1 != 0`, then infinitely many prime-indexed ghosts are nonzero. More precisely,

`g_p = g_1 mod p`

for every prime `p`; therefore `g_p != 0` for every prime `p>|g_1|`.

This is the exact integral mechanism behind the all-depth requirement. It is stronger than saying
that a chosen finite completion failed: every nontrivial integral determinant class has an
infinite ghost history.

## 4. Rational vacuum isolation and analytic collapse

Allow rational Euler multiplicities `q_n in Q`. Fix `lambda in Q` and demand the pure vacuum ghost

`h_1=lambda`, `h_m=0` for `m>1`,

where `h_m=sum_(d|m)d q_d`.

### Theorem IWG-4 (unique rational vacuum lift)

The unique solution is

`q_n = lambda mu(n)/n`.

#### Proof

Weighted Möbius inversion gives

`n q_n = sum_(d|n) mu(n/d) h_d = lambda mu(n)`. QED.

If `lambda` is a nonzero integer, this lift is not integral: for every prime `p` not dividing
`lambda`, `q_p=-lambda/p` is nonintegral.

### Theorem IWG-5 (Möbius vacuum product)

On `|z|<1`, with logarithms defined by their power series,

`product_(n>=1) (1-z^n)^(lambda mu(n)/n) = exp(-lambda z)`.

The logarithmic series converges normally on compact subdiscs. Indeed

`log(1-z^n) = -sum_(r>=1) z^(nr)/r`,

so the coefficient of `z^m` in the logarithm of the product is

`-(1/m) sum_(n|m) n q_n = -lambda` for `m=1` and `0` otherwise.

Thus perfect diagonal cancellation erases every divisor and leaves a zero-free exponential. Its
fractional Euler multiplicities are not an integral single-valued divisor decomposition across
the cyclotomic boundary.

## 5. Completion-anomaly class

For a rational ghost profile `g=(g_n)`, define

`A_n(g) = (1/n) sum_(d|n) mu(n/d) g_d mod Z in Q/Z`.

Then:

1. `A` is additive;
2. `A(g)=0` exactly when the rational Euler coordinates lift integrally;
3. for the pure vacuum `lambda delta_1`,
   `A_n = lambda mu(n)/n mod Z`;
4. a nonzero integral vacuum has nontrivial obstruction at every sufficiently large prime.

This quotient class is the precise completion anomaly: rational polarization gives a desired
ghost profile, while `A` measures failure to descend to integral determinant torsion.

## 6. Fusion with the cofinal counterdivisor theorem

The earlier theorem ULF-CIT-2 says persistent local residue-cell torsions accumulate roots at
`1`, so a nonzero entire completion requires a cofinally growing negative counterdivisor. IWG says:

- cancelling all but finitely many ghosts integrally is impossible;
- cancelling them rationally is unique and collapses to a zero-free exponential;
- therefore a nonzero divisor-bearing completion must retain infinitely many integral ghost
  degrees while the negative interaction divisor grows cofinally.

Consequently the completed Xi torsion cannot be the scalar sum/product of local completion
indices, a finite-jet renormalization, or the exponential of the known cubic current. It must be
an all-depth interaction torsion formed before scalar determinant evaluation.

## 7. Fourth-organ predictions

1. Any genuine Deninger/TR/determinant realization with a nonzero vacuum class must exhibit an
   infinite sequence of iterate traces satisfying `g_(mp)=g_m mod p`; a finite trace truncation
   cannot be the source object.
2. The existing cross-pair compensator's degree-two cancellation cannot extend to annihilation of
   every higher ghost inside an integral Witt class unless the whole class is trivial. A surviving
   extension must redistribute, not erase, the physical ghost through infinitely many degrees.
3. Any recurrence realization of the same completion must have open lifted history at infinitely
   many prime-power depths; finite-state closure can only be an observer quotient.
4. Any scalar cubic/Gamma-Wold current can be at most one ghost moment of the counterchannel, never
   its determinant torsion.

## 8. Relation to RH

This theorem does not prove RH. It removes a whole source-model class from the final architecture.
A closing theorem must construct the literal successor--dilation interaction tail integrally,
identify its analytic determinant before divisor specialization, and prove its effective torsion
is supported on the reflection-fixed locus. Krein--Langer then converts absence of off-wall torsion
into zero excess negative index and RH.

What IWG changes is the type of that missing object: it must be an integral, infinitely supported,
interaction-level completion, not a finite index, scalar renormalization, or rational Möbius
counterterm.
