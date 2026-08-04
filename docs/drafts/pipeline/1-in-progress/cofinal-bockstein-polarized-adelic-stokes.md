# Cofinal Bockstein polarized adelic Stokes

- **Stage:** 1-in-progress
- **Status:** `[CONJECTURE] [OPEN CORE]`
- **Active claim:** construct and prove an unconditional arithmetic Stokes law annihilating the
  explicit physical cofinal Bockstein class in
  `MobiusThetaPhysicalParacyclicSourceNullHomology.lean`.

## Exact target

For every `n >= 2`, Xi divisor support `rho`, ordinary prime `p`, and Tate stage `m`, prove

```text
ccmMobiusThetaCofinalSourceHomologyLanding n
  (xiSupportMultiplicity rho) m (rho : C)
  (xiSpectralPointSupport rho)
  (ccmRationalAdelicOrdinaryPrimeCycleAtom p) = 0.
```

The existing coefficient reader proves this is equivalent to `Re(rho)=1/2`; global target proves
RH. No RH-equivalent condition may occur as a premise.

## Established frontier

- `[CORPUS]` relative group is one-dimensional and its generator is nonzero.
- `[CORPUS]` physical class reads
  `(deningerHalfDensityMateGain n rho - 1) * firstNonzeroXiJet * primeTrace`.
- `[CORPUS]` first nonzero Xi jet and ordinary-prime trace are nonzero.
- `[CORPUS]` finite and archimedean Haar characters cancel on full rational adelic source,
  producing literal Haar trace `epsilon_1` and reduced cyclic source `ker epsilon_0 intersect ker epsilon_1`.
- `[LOCAL-RESEARCH]` finite interval exactness, ordinary cofinal inclusion, mixed cobar exactness,
  regular Meyer--Poisson boundary membership, and relation-kernel exactification do not annihilate
  the coefficient faithfully.

## First hostile discriminator

Write source-inverse and analytic-adjoint positive characters as

```text
alpha_rho(n) = n^(1/2-Re(rho)),
beta_rho(n)  = n^(Re(rho)-1/2).
```

Adelic product formula gives `alpha_rho(n) * beta_rho(n) = 1` for every spectral parameter.
Physical Bockstein vanishing requires `alpha_rho(n) = beta_rho(n)`. Any proposal deriving only
reciprocity, full-product gain one, or zero after trace-erasing completion is `[FALSIFIED]` as an
RH argument.

## Active conjecture

`[CONJECTURE — POLARIZED_ADELIC_STOKES]` There is a global source-pointed singular comparison,
defined before divisor specialization, from the reduced rational adelic cyclic source to the
Gamma/co-Poisson top-conormal target such that:

1. its two endpoint residues are the source-inverse and analytic-adjoint characters separately;
2. the source Real/cyclic symmetry identifies the two residues without inverting the prime label;
3. the comparison is coefficient-faithful on the ordinary-prime top atom;
4. its Stokes boundary is zero in the retained, non-trace-erasing cofinal quotient.

These four clauses would force `alpha_rho=beta_rho`, hence vanish the explicit class.

## Open core

`[OPEN CORE]` Construct clause (2) from literal arithmetic source data. Existing Real structure
conjugates while rational scaling inversion changes `p` to `p^-1`; that proves reciprocity, not
same-prime equality. A valid proof must supply a non-divisor-fitted polarization which removes this
inversion without assuming unitary modular character.

## Failure log

- Full adelic Haar cancellation: kills total product character only; does not kill physical ratio.
- Direct-limit inclusion: sends every top output to zero one stage later; maximally trace-erasing.
- Regular Meyer boundary: fixed Gaussian source is not in boundary range; membership is equivalent
  to desired scalar vanishing.
- Baumslag exactification: lowers nonzero cup to faithful relation-kernel character; does not
  annihilate it.

## 2026-08-03 hostile closure of the pointwise Fourier--Real conjecture

`[FALSIFIED]` The displayed `POLARIZED_ADELIC_STOKES` conjecture cannot be obtained from the
currently formalized source Real structure and functional-equation Fourier symmetry.  The actual
CCM Real involution is coefficientwise and preserves the rational scaling label.  Fourier/Poisson
reflection is the operation which inverts dilation and exchanges the spectral fibres
`s` and `1-s`.  Its square closes the reflected two-point orbit; it does not identify the two
characters inside one fibre.  Treating that orbit exchange as same-prime pointwise equality would
assume the RH-bearing conclusion.

The finite/cofinal alternatives do not repair this failure.  Ordinary closed completion erases
the retained class, while the explicit cofinal quotient retains a one-dimensional generator whose
physical coefficient is exactly `gain - 1`.  Enlarging the boundary by that generator makes the
quotient vanish for every parameter, not only at Xi zeros.

## Frozen successor: actual-edge relative ideal provenance

Let

```text
d_p = primeFirstTraceEssentialSourceDeviation p,
c_p = d_p(2) = 1/p - p/(farPrime p)^2.
```

The proved bounds `3/(4p) <= c_p <= 1/p` show that `c=(c_p)` is the canonical prime-harmonic
relative edge.  For a real modular displacement `t`, put

```text
c_t(p) = p^t c_p.
```

`[PAPER-PROVED POSITIVE SURVIVOR]` The actual edge has the exact reflected trace-ideal fracture

```text
Summable c_t       <-> t < 0,
Summable c_(-t)    <-> t > 0,
(Summable c_t <-> Summable c_(-t)) <-> t = 0.
```

Moreover `1/p-c_p=p/(farPrime p)^2` is summable, so `[c]=[1/p]` modulo `ell1`, independently of
the far-prime presentation.  This is the actual strict-preclosure edge, not the previously known
raw model `p^(-sigma)`.

`[CONJECTURE -- ORDINARY_PRIME_POLARIZED_IDEAL_PROVENANCE]` Construct before divisor
specialization one completed ordinary-prime source class and one literal Gamma/co-Poisson Fourier
comparison such that, after specialization at every Xi Cartier stalk:

1. the two endpoint images are the actual twists `c_t` and `c_(-t)`, with
   `t=2 Re(rho)-1`;
2. both images retain the same nonzero source ancestry modulo trace class;
3. the comparison preserves trace-class membership because it is induced by one source-defined
   Morita/Fourier correspondence, not by a divisor-fitted identification;
4. multiplicity jets travel in a separate compatible filtration.

Clauses 1--3 plus the exact fracture force `t=0`.  Clause 3 is not supplied by the current CCM
Real structure: Real preserves scaling degree, whereas Fourier supplies reflection by swapping
fibres.  The missing producer is therefore the completed Fourier--Morita action on the retained
relative ideal, together with proof that it transports one ancestral class rather than two
unrelated reflected classes.

### Circularity falsifier

It is invalid to define both endpoint twists from `rho` and then declare them images of one class.
The comparison must be constructed on the literal reduced adelic source, before Xi specialization,
and its ideal preservation must follow from an explicit operator/correspondence theorem.  Without
that construction the conjecture is another exact RH criterion, not a proof.

## Dependency-closed proof of the actual-edge law

Fix an ordinary prime `p`, put `P=p`, and write `R=farPrime(p)`.  The construction gives
`P >= 2` and `R >= P^2`.  Its retained coordinate is

```text
c_p = 1/P - P/R^2.
```

Since `R^2 >= P^4 >= 4P^2`,

```text
0 <= P/R^2 <= 1/(4P),
3/(4P) <= c_p <= 1/P.                                      (E1)
```

Also `R^2 >= P^4` gives

```text
0 <= 1/P-c_p = P/R^2 <= 1/P^3.                             (E2)
```

The prime-cubic majorant is summable, so (E2) proves that the actual edge and prime harmonic edge
define the same class modulo `ell^1`.  In particular, every allowed far-prime presentation has the
same quotient class: changing the auxiliary far-prime witness changes `c` by an `ell^1` sequence.

For `t in R`, set `c_t(p)=P^t c_p`.  All terms are nonnegative.  If `t<0`, (E1) and the real-power
law give

```text
0 <= c_t(p) <= P^t/P = P^(t-1).
```

Here `t-1 < -1`; the prime real-power series is summable.  Hence `c_t` is summable.  Conversely, if
`t>=0`, then `P^t>=1`, so (E1) gives

```text
c_t(p) >= c_p >= (3/4)/P.
```

Euler's prime harmonic divergence excludes summability.  Therefore

```text
Summable(c_t) <-> t<0.                                     (E3)
```

Applying (E3) to `-t` gives `Summable(c_(-t)) <-> t>0`.  The two trace-class truth values agree
exactly at `t=0` (where both fail), and they can never both hold.  No divisor, zero, functional
equation, positivity postulate, or spectral conjecture enters this proof.

## Antagonistic scope audit

- **Proved:** literal strict-preclosure edge carries a presentation-independent nonzero class in
  `ell^2/ell^1`; modular twisting has an exact, reflected trace-ideal phase transition at `t=0`.
- **Not proved:** a Gamma/co-Poisson or CCM correspondence sends one source-defined ancestral class
  to both reflected twists.  Equality of their trace-ideal status is therefore not yet available
  at Xi divisor points.
- **Why this is not decorative:** unlike a scalar RH equivalence, (E1)--(E3) is unconditional and
  identifies the exact ideal-valued invariant which any successful physical comparison must
  preserve.  It simultaneously explains Hilbert--Schmidt survival, trace-class failure, reflected
  one-sidedness, and auxiliary far-prime independence.
- **Kill condition for the successor:** if literal Fourier/Morita comparison swaps unrelated source
  fibres, erases the `ell^2/ell^1` class, or preserves only reciprocal product gain, then it cannot
  supply clause 3 and this successor route remains open rather than proving RH.

## Source provenance found: occupancy Fisher equals the essential edge modulo trace class

The apparent gap between the activation/Möbius/Gamma source and the strict-preclosure edge is not
real.  Put `q_p=1/p` and let

```text
F_p = q_p/(1+q_p)^2
    = (xiMobiusPrimeSchurValuationDamping p)^2.
```

The second equality is the already proved activation-disintegration law: `F_p` is simultaneously
squarefree occupancy Fisher information and the square of the Möbius-to-Gamma damping.  Direct
algebra gives

```text
0 <= 1/p-F_p = (2p+1)/(p(p+1)^2) <= 3/p^2.                 (F1)
```

Together with (E2),

```text
|c_p-F_p| <= |1/p-F_p| + |1/p-c_p| <= 4/p^2.              (F2)
```

For the modular twists `c_t(p)=p^t c_p` and `F_t(p)=p^t F_p`, positivity of real powers and (F2)
give

```text
|c_t(p)-F_t(p)| <= 4 p^(t-2).
```

Hence, whenever `t<1`, the difference `c_t-F_t` is in `ell^1`.  Every Xi divisor lies in the open
critical strip, so its centered rate `t_rho=2 Re(rho)-1` satisfies `|t_rho|<1`.  Consequently both
reflected actual edges have literal source representatives modulo `ell1` in the full prime-sequence
module:

```text
[c_(t_rho)]  = [F_(t_rho)]  modulo ell^1,
[c_(-t_rho)] = [F_(-t_rho)] modulo ell^1.                 (F3)
```

This closes clauses 1 and 2 of `ORDINARY_PRIME_POLARIZED_IDEAL_PROVENANCE`: the two endpoint
classes are no longer unrelated analytic decorations.  They are modular transports of one
ordinary-prime Fisher density already selected by diagonal Wold activation, squarefree occupancy,
Möbius depth differences, and Gamma valuation damping.

It does **not** place both twists in one fixed `ell2/ell1` quotient.  The exact formalized Fisher
threshold is

```text
sum_p F_t(p)^2 < infinity                     <-> t < 1/2,
sum_p F_t(p)^2, sum_p F_(-t)(p)^2 < infinity <-> |t| < 1/2. (F4)
```

Thus the whole Xi critical strip `|t|<1` is too large for one common prime `ell2` carrier.  The
outer half-strips are genuine topology escape, not missing estimates.

### Sharpened sole open producer

The current algebraic CCM Morita representation cannot prove the remaining conservation law.  It
lands entirely in trace-class operators, while (E3) says the retained critical Fisher/essential
class is not trace class.  Its ordinary trace and higher restriction formulas therefore consume
an `ell^1` orbit coefficient before the relative class is formed.  The coefficientwise CCM Real
structure preserves scaling degree; analytic Fourier reflection swaps fibres; neither acts on the
retained `ell^2/ell^1` class.

The exact remaining statement is now:

`[OPEN CORE -- GRADED POLARIZED FISHER-IDEAL CONSERVATION]` Construct, before divisor
specialization, a graded/variable-ideal completion of the literal adelic source whose neutral
fibre contains `[F]`, and a source-inverse/analytic-Fourier correspondence between its reflected
fibres such that at every Xi divisor its endpoint maps are `[F_t]` and `[F_-t]` and the
correspondence preserves membership of `ell^1`.  It may not replace these fibres by one fixed
Hilbert completion: (F4) proves that such a carrier does not exist across the whole strip.  Then
(E3) and (F3) force `t=0`, hence RH.

This is strictly narrower than “construct a source” or “prove positivity.”  Source, arithmetic
atom, Gamma ancestry, non-erasure class, both endpoint representatives, critical-strip
moderateness, and ideal classifier are now explicit.  Missing mathematics is one polarized
conservation theorem on a singular relative ideal.  Defining that conservation by declaring the
two endpoint statuses equal is circular; it must follow from a literal Fourier/cyclic operator or
correspondence on the completed arithmetic source.

## 2026-08-04 fixed-Hilbert Fisher completion falsified

`[FALSIFIED]` The polarized Fisher comparison cannot be defined on one fixed prime `ell2/ell1`
completion over the full Xi critical strip.  The source-selected density has the exact formula

```text
F_t(p) = p^t * p/(p+1)^2,
1/4 * p^(t-1) <= F_t(p) <= p^(t-1).
```

Euler's prime-power criterion gives the sharp laws (F4), formalized in
`PrimeFirstTraceEssentialEdgeReflectedIdealGrade.lean`.  Since Xi supplies only `|t|<1`, not
`|t|<1/2`, some admissible divisor fibres leave every proposed common `ell2` carrier.

**Strongest positive survivor.**  The trace-ideal classifier survives unchanged:
`F_t in ell1 <-> t<0`.  What changes is the representation.  A viable singular Cartier object
must be a graded variable-ideal/off-diagonal correspondence carrying reflected fibres, with
`ell1` as the conserved subobject; it cannot be an ordinary bounded operator, one fixed Hilbert
completion, or a two-sided-singular relation without additional source invariance.  The new
`two-sided-singular-gelfand-defects` manuscript reinforces the last point: abstract countable
noncoercive observers admit large common closed avoidance spaces, so singularity alone supplies no
selection.

## 2026-08-04 strict cyclic-provenance audit

The new source-dagger manuscript and
`MobiusThetaPhysicalParacyclicSourceNullHomology.lean` sharpen the scalar obstruction but do not
yet construct the chain-level source claimed by the phrase “source-null-homology.”  Precisely:

- `CCMRationalAdelicDegreeOneCyclicSource` is the degree-one cyclic-bar tensor object;
- the ordinary-prime object is proved to have product trace one, but is not proved to lie in the
  kernel of the Hochschild degree-one boundary;
- the product reporter is invariant under cyclic rotation, but the same formal module proves it
  does not annihilate all degree-two Hochschild boundaries when the unit trace is nonzero;
- `ccmMobiusThetaCofinalSourceHomologyLanding` is a linear map directly scaled by the Xi jet and
  the product reporter; it is not proved to factor through Hochschild/cyclic homology or to be a
  component of a strict chain map.

Therefore the current one-dimensional Tate cokernel is a correct retained obstruction quotient,
but calling its old product-trace input a cyclic homology class would be theatre.

The missing chain producer is now constructed and formalized in
`CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean`.  The prime zero-isotropy relative complex
has unconditional `D_1 D_0=0`; its ordinary-prime class is retained by a Schwartz fixed-vector
theorem; and a strict prime-faithful chain map sends it nontrivially to the resolved actual-Xi
complex, where it is annihilated.  The formal classification also proves that this image is a
target boundary.  Thus strict rational-adelic provenance is closed, but the physical/scalar
cofinal landing is not: the open Bockstein/Route-R theorem must compare this resolved boundary to
the singular coefficient-faithful Cartier quotient without replacing the comparison by the
RH-equivalent statement that the physical coefficient vanishes.

The source class now also has an independent normalized Stokes period in
`CCMRationalAdelicPrimeIsotropyStokesRegulator.lean`.  The bilateral prime orbit sum converges at
both archimedean ends and satisfies `R_p(alpha_p x-x)=epsilon_0(x)` on the actual adelic core.
Hence `I_p(y,z)=z-R_p(y)` kills every relative boundary and descends to `H^1` with
`I_p([eta_p])=1`.  Source Stokes flatness and class retention are therefore closed without using
Xi.  This makes the remaining obstruction sharper: the strict Xi image is nevertheless a target
boundary, so missing Cartier step cannot be an ordinary boundary-preserving cohomology map.  It
must be a source-constructed singular/secondary comparison retaining the chosen Xi primitive and
the graded `ell1` subobject; declaring its physical anomaly zero is still exactly RH.
