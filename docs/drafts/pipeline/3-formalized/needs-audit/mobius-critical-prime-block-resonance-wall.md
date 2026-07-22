# Möbius critical prime-block resonance wall

- **ID:** `mobius-critical-prime-block-resonance-wall`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / NO-GO / BRIDGE
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [CANDIDATE NEW FORMULATION] [NOVELTY NOT CERTIFIED] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/MobiusCriticalPrimeBlockResonance.lean`
- **Statement:** A terminal block of critical Möbius Euler factors has simultaneous forward and
  inverse amplification at moving frequencies tending to zero; hence no absolute Fourier,
  translation-invariant multiplier, or fixed positive Gamma-weight estimate can uniformly control
  the prime-removal cascade.

## Goal

Test the prime-by-prime rough-Möbius Laplace cascade as an unconditional provider for the
half-plane decay required by `MobiusLaplaceCriterionFrontier.lean`.  The proposed provider was a
uniform positive norm bound for successive critical factors

```text
T_p = I - p^(-1/2) U_(log p).
```

This card isolates the strongest non-circular theorem left after that provider fails.  It does not
estimate the Möbius Laplace transform and cannot imply RH by itself.

## Gates

- [x] 0 → 1 in-progress: exact source, attack, falsifier, and literature boundary identified
- [x] 1 → 2 fully-proven: complete paper proof below; no RH or numerical input
- [x] 2 → 3 formalized: exact finite-window inequality and Chebyshev budget in Lean
- [ ] 3 → 4 publication-ready: blocked on independent novelty/significance review

## Exact rough-prime recurrence

For a finite set `P` of primes, put

```text
F_P(x) = sum_(n>=1, (n, product P)=1) mu(n) exp(-n x).
```

If `p` is prime and `p notin P`, splitting the `P`-rough integers according to divisibility by `p`
gives

```text
F_P(x) = F_(P union {p})(x) - F_(P union {p})(p x).       (1)
```

Indeed, every term divisible by `p` is `n=pm`; the squareful terms have Möbius value zero, and on
the remaining terms `mu(pm)=-mu(m)`.  For the critical logarithmic profile

```text
G_P(y)=exp(-y/2)F_P(exp(-y)),
```

equation (1) becomes

```text
G_P(y)=G_(P union {p})(y)
       -p^(-1/2)G_(P union {p})(y-log p).                 (2)
```

Thus every prime-removal step is the critical translation factor

```text
T_p=I-p^(-1/2)U_(log p).                                  (3)
```

Each individual factor is invertible because `p^(-1/2)<1`, but this does not give a uniform
all-prime inverse.

## Synchronized terminal-block theorem `[PROVED HERE]`

For `Y>1`, let

```text
W_Y={p prime : Y/3<p<=Y},
t_Y=pi/log Y,
B_Y(t)=product_(p in W_Y)(1-p^(-1/2)exp(-i t log p)).      (4)
```

Then

```text
|B_Y(t_Y)|^2 >= (1+Y^(-1/2))^(#W_Y),                      (5)
product_(p in W_Y)|1-p^(-1/2)|^(-1)
  >= exp(#W_Y/Y^(1/2)).                                   (6)
```

Moreover Chebyshev's elementary bounds imply

```text
#W_Y >> Y/log Y,                                          (7)
```

so both sides in (5)--(6) diverge at least like

```text
exp(c sqrt(Y)/log Y)                                      (8)
```

for some absolute `c>0` and all sufficiently large `Y`.  Since `t_Y -> 0`, every continuous
positive archimedean weight at zero, including the standard Gamma density, leaves the moving
resonance unbounded.

### Proof of the forward bound

For `Y>=27` and `p in W_Y`,

```text
2pi/3 < t_Y log p <= pi.
```

Cosine is decreasing on `[0,pi]`, hence

```text
cos(t_Y log p) <= cos(2pi/3)=-1/2.
```

Writing `r=p^(-1/2)` gives the exact identity

```text
|1-r exp(-i t_Y log p)|^2
  =1+r^2-2r cos(t_Y log p)
  >=1+r^2+r
  >=1+Y^(-1/2).                                          (9)
```

Multiply (9) over the finite window to obtain (5).

### Proof of the inverse bound

At frequency zero, `0<r<1` and `-log(1-r)>=r`.  Since `p<=Y`, every `r>=Y^(-1/2)`.  Therefore

```text
log product_(p in W_Y)(1-p^(-1/2))^(-1)
  =sum_(p in W_Y)-log(1-p^(-1/2))
  >=#W_Y Y^(-1/2),                                       (10)
```

which is (6).

### Prime-window growth

The existing exact window theorem `windowPrimes_card_ge`, applied with `x=Y/3` and `y=Y`,
gives

```text
[(Y-1)log2-log(Y+2)-2sqrt(Y)logY-(log4)Y/3]
  <= #W_Y logY.                                          (11)
```

The bracket is at least `(log2/2)Y` for all sufficiently large `Y`, proving (7).  Finally
`log(1+u)>=u/2` for sufficiently small positive `u`; (5), (7), and (10) give (8).

## Operator consequence

On any translation-invariant Hilbert realization, Fourier transform turns the finite operator

```text
product_(p in W_Y)(I-p^(-1/2)U_(log p))
```

into multiplication by `B_Y(t)`.  Its norm is at least `|B_Y(t_Y)|`.  Its inverse multiplier at
zero is exactly the product in (6).  Thus the block condition number is exponentially large on the
critical scale.  The resonance occurs at `t_Y=pi/logY`, not at large frequency, so multiplying by
a fixed Gamma factor cannot repair it.

This kills any proof that takes absolute values, a supremum norm, an `L2` multiplier norm, or a
fixed positive spectral weight before the prime-block cancellation has occurred.  It does not kill
a signed non-translation-invariant renormalization or an estimate after projecting out the moving
low-frequency chamber.

## Hostile attack and exact limit

1. **Order primes differently.** A cofinal ordering still contains arbitrarily large terminal
   windows.  Commuting translation factors make regrouping ineffective in every positive
   multiplier norm.
2. **Use Gamma damping.** The bad frequency tends to zero, where the Gamma density is finite and
   strictly positive.
3. **Use `L2` instead of `L-infinity`.** Multiplication-operator norm is essential supremum; continuity
   of the finite multiplier turns the point witness into a positive-measure neighborhood.
4. **Invert one prime at a time.** Every step is invertible, but (6) proves the cofinal inverse is
   not uniformly conditioned.
5. **Use Buchstab/fundamental-lemma positivity.** Existing corpus already locates a surviving
   balanced Type-II chamber.  The synchronized block theorem is its critical translation analogue:
   positive norms preserve rather than cancel that chamber.

## No-go closure

- **Exact killing theorem/mechanism:** simultaneous terminal-block phase alignment (5) and
  zero-frequency inverse amplification (6), with Chebyshev supply (7).
- **Strongest positive survivor:** resonance has a forced moving scale `t=Theta(1/logY)` and a
  quantitative size `exp(Theta(sqrt(Y)/logY))`; this classifies the missing cancellation as a
  low-frequency, signed, cross-prime effect.
- **New insight:** successful Möbius--Laplace source theorem must cancel the terminal block before
  entering any positive norm, or use a source-defined projection/renormalization that removes the
  moving `1/logY` chamber.  Primewise contraction and fixed archimedean damping are structurally
  insufficient.
- **Status:** paper proof dependency-closed and formalized.  Exact moving-window formulation was not
  found in searched sources; novelty remains uncertified because it is an elementary consequence
  of established finite-Euler-product and Chebyshev methods.

## Internal corpus boundary

- `MobiusLaplaceCriticalDilationNoGo.lean` proves divergence of the absolute critical prime mass;
  it does not exhibit a simultaneous finite-block frequency or the `1/logY` moving resonance.
- `HardyTitchmarshEulerConcrete.lean` proves each local factor is invertible and realizes its
  weighted spectral multiplier; it does not prove cofinal block conditioning.
- `WindowBudget.lean` supplies (11).
- `PrimeClockFiniteScaling.lean` and `PrimeClockCriticalProfile.lean` prove a different
  `1/logN` reflection-displacement window in which clock phase cancels.
- `critical-multiplicative-compensated-cancellation-rh.md` proves the Buchstab/Type-II parity
  obstruction but not the critical translation resonance above.

## Lean certificate

`MobiusCriticalPrimeBlockResonance.lean` proves:

- `mobiusCriticalPrimeFactor_eq_archimedeanLocalMultiplier` — exact connector to physical
  Hardy--Titchmarsh local multiplier;
- `normSq_mobiusCriticalPrimeFactor` — local cosine law;
- `mobiusCriticalPrimeWindow_cos_le_neg_half` — synchronized moving-frequency chamber;
- `mobiusCriticalPrimeBlock_norm_sq_lower` — forward block bound (5);
- `mobiusCriticalPrimeInverseBlock_lower` — inverse block bound;
- `mobiusCriticalPrimeWindow_card_budget` — exact Chebyshev budget (11);
- `mobiusCriticalPrimeBlock_resonance_wall` — combined endpoint.

Direct `lake env lean` and final
`lake build GaloisForLFunctions.RHTower.MobiusCriticalPrimeBlockResonance` pass.  Endpoint axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Literature boundary

- Keith Conrad, *Partial Euler Products on the Critical Line*, studies fixed critical-line
  arguments and reduces product convergence to prime sums.  The moving terminal-block frequency
  `pi/logY` and the two-sided cascade condition number above are not stated in the inspected paper.
- S. M. Gonek, *Finite Euler products and the Riemann Hypothesis*, arXiv:0704.3448, studies weighted
  finite Euler approximations and their relation to zeros; it does not state (5)--(8).
- J. Friedlander and H. Iwaniec, *Asymptotic sieve for primes*, arXiv:math/9811186, and
  K. Ford and J. Maynard, *On the theory of prime producing sieves*, arXiv:2407.14368, delimit the
  parity/Type-II obstruction.  They motivate the signed survivor but do not provide this Laplace
  translation-block theorem.

No absence-of-match search is a novelty proof.

## Log

- 2026-07-22 — exact rough-prime recurrence, synchronized terminal-block theorem, hostile attack,
  and literature boundary recorded; no computation used.
- 2026-07-22 — finite forward/inverse lower bounds, exact physical multiplier connector, and
  Chebyshev window budget formalized; targeted build and axiom audit pass.
