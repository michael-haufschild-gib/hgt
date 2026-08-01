# Hedenmalm prime-normal Wick boundary energy

- **ID:** `hedenmalm-prime-normal-wick-boundary-energy`
- **Stage:** 5-failed
- **Type:** SOURCE-NORMAL ALL-PRIME CALIBRATION THEOREM / RETIRED RH ROUTE
- **Scientific status:** `[PAPER THEOREM PROVED HERE] [LEAN CALIBRATION FORMALIZED]`
  `[CORPUS COLLISION] [STRICT-DESCENT ROUTE RETIRED] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/needs-audit/hedenmalm-two-prime-theta-interval-normal-frame.md`;
  - `../3-formalized/not_new_scientific_knowledge/prime-clock-critical-window-scaling.md`;
  - `../2-fully-proven/not_new_scientific_knowledge/prime-superspace-wick-anisotropy-decompactification.md`;
  - `../2-fully-proven/needs-audit/hedenmalm-quantile-volterra-universal-boundary-defect.md`.
- **RH used:** no.
- **Computation used:** no.

## Question

The Hedenmalm source-normal frame has algebraic prime rank two, but every finite or summably
weighted diagonal Hilbert frame has arbitrarily deep simultaneous prime-phase recurrences.  What
happens at the forced nonsummable all-prime boundary?

The answer joins two previously separate corpus objects exactly.  The squared norm of the
Hedenmalm prime-normal row is the sum of the vertical prime-clock energy and the radial reflected
prime-clock energy.  The finite-energy locus of its prime-harmonic renormalization is exactly the
real centered spectral axis.

## Source-normal row

For each prime `p`, the centered theta-interval anomaly has normal multiplier

```text
a_p(z)=2 p^(-1/2) sin(z log(p)/2)/z.
```

Since `XiC(0) != 0`, multiplication by `z` is a unit on the Xi divisor scheme.  Thus the rescaled
row

```text
b_p(z)=z a_p(z)=2 p^(-1/2) sin(z log(p)/2)                 (1)
```

retains every Xi conormal and every multiplicity jet.  In particular, the already proved
prime-2/prime-3 no-common-zero theorem remains valid on every Xi root block.

For `X>=2`, put

```text
H_X = sum_(p<=X) 1/p,
E_X(z)=sum_(p<=X)|b_p(z)|^2.                              (2)
```

These objects use literal rational primes and the theta translation anomaly before any zero is
chosen.

## Theorem: exact Wick decomposition `[PROVED HERE]`

Write `z=x+i y`.  Then

```text
E_X(z)=V_X(x)+R_X(y),                                    (3)

V_X(x)=4 sum_(p<=X) sin^2(x log(p)/2)/p,
R_X(y)=4 sum_(p<=X) sinh^2(y log(p)/2)/p.
```

### Proof

For real `u,v`,

```text
|sin(u+i v)|^2=sin^2(u)+sinh^2(v).                       (4)
```

Apply `(4)` with `u=x log(p)/2`, `v=y log(p)/2`, multiply by `4/p`, and sum over
the primes.  The two resulting terms are exactly the corpus vertical and radial prime-clock
energies.  `QED`

Equation `(3)` is not an analogy.  It identifies the newly constructed Hedenmalm normal frame
with the previously formalized Wick-anisotropic prime superspace term by term.

## Theorem: finite prime-harmonic energy selects the real axis `[PROVED HERE]`

For every `z in C`,

```text
limsup_(X->infinity) E_X(z)/H_X < infinity
  iff Im(z)=0.                                             (5)
```

More precisely:

```text
y=0       => 0 <= E_X(z)/H_X <= 4,
y!=0      => E_X(z)/H_X -> infinity.                      (6)
```

For real `x!=0`, natural prime ordering gives the sharper asymptotic

```text
E_X(x)/H_X -> 2.                                          (7)
```

### Proof

If `y=0`, equation `(3)` and `sin^2<=1` give `E_X(z)<=4H_X`.

For arbitrary real `y`, `|sinh t|>=|t|` gives

```text
R_X(y)>=y^2 chi_X,
chi_X=sum_(p<=X)(log p)^2/p.                              (8)
```

The proved Mertens asymptotics are

```text
chi_X~(1/2)(log X)^2,
H_X~log log X.                                            (9)
```

Hence `chi_X/H_X -> infinity`; `(8)` proves the second clause of `(6)` for `y!=0`.
This proves `(5)`.

For fixed real `x!=0`, the prime number theorem and partial summation give convergence of
`sum_p p^(-1-i x)` in natural prime order.  Since

```text
V_X(x)=2H_X-2 Re sum_(p<=X)p^(-1-i x),                   (10)
```

and `H_X->infinity`, division by `H_X` proves `(7)`.  `QED`

## Root-block consequence

Let `zeta` be a centered Xi zero and `f_zeta` its nonzero, source-normalized Hedenmalm right mode.
The source-normal interval theorem gives the root-block row

```text
(b_p(zeta) f_zeta)_p.                                    (11)
```

At least one of its prime-2/prime-3 entries is nonzero.  Equations `(5)`--`(6)` give

```text
sup_X [1/H_X sum_(p<=X)||b_p(zeta)f_zeta||^2] < infinity
  iff Im(zeta)=0.                                        (12)
```

Since `zeta=-i(rho-1/2)`, the right side is `Re(rho)=1/2`.  Thus `(12)` is a literal
ordinary-prime normal-frame criterion for each Xi root block, not a divisor-fitted norm.

## Universal interpretation

Equation `(3)` identifies what the corpus had been seeing in separate charts:

```text
finite prime frame:
  vertical clock recurrence can make every finite row nearly disappear;

all-prime nonsummable boundary:
  recurrent vertical energy grows only like H_X,
  while any radial/off-line component costs chi_X >> H_X;

Hedenmalm source-normal blow-up:
  supplies the conormal row which ordinary L2 erased;

prime-harmonic renormalization:
  retains critical rows and expels every off-line row.
```

The universal law is therefore a Wick decomposition followed by a scale-separation law:

> **At the source-normal all-prime boundary, clock recurrence has prime-harmonic cost, while
> radial reflection has Fisher-susceptibility cost.  Their growth scales are inequivalent, so
> finite renormalized normal energy forces zero radial charge.**

This explains simultaneously why every finite-prime argument recurs, why summable diagonal
frames fail, why the all-prime limit is necessary, and why the missing completion must be
nonsummable and source-normal rather than an ordinary Hilbert direct sum.

## Retired conjecture: strict prime-normal boundary descent

`[RETIRED] [HEDENMALM_PRIME_NORMAL_STRICT_DESCENT]`

> The source-normal map generated by the centered theta-interval anomalies extends from the
> exponential Hedenmalm core to a closed reflection-compatible Besicovitch boundary row with
> seminorm
> 
> ```text
> ||(v_p)||_partial^2=limsup_X H_X^(-1) sum_(p<=X)||v_p||^2,
> ```
> 
> and every source-normalized Xi root block maps to `(11)` as a nonzero vector in its finite
> domain, including its complete Jordan/multiplicity tower.

The primes, theta intervals, normalization `H_X`, reflection, and source modes are fixed before
any zero.  Nevertheless this is not a new provider theorem.  The corpus already constructs the
same radial selector in the prime-valuation Kakutani polar completion and proves that the missing
source-to-sector normality is RH-equivalent.  By `(12)`, the asserted descent implies RH
immediately; no independent source argument for it was found here.

## Exact surviving open core

The missing theorem is now one uniform source estimate, not construction of another conormal:

```text
for every root-block vector f in the closed theta Grushin domain,
sup_X H_X^(-1) sum_(p<=X)||A_p(B)f||^2 < infinity,        (13)
```

where `A_p(mu)=2 p^(-1/2) mu sin(log(p)/(2mu))` is the already proved essential reciprocal
symbol and the source-normal convention removes the harmless common factor `mu` on each nonzero
root block.  Formula `(13)` must be proved on the source domain before spectral specialization.
Assuming it only on named root vectors is equivalent to RH by `(12)`.  The recurrence paper does
not supply this estimate: its countable theorem requires strictly positive summable probe
weights, whereas the selector here uses the divergent prime-harmonic mass `sum_p 1/p`.

## Hostile audit

1. **Not RH.**  The cross-chart identity and finite-energy classification do not prove that the
   theta root expansion lies in the finite Besicovitch domain.
2. **Not a disguised finite frame.**  `H_X` diverges.  Every finite and every summably weighted
   diagonal frame remains excluded by the existing recurrence theorem.
3. **Not ordinary L2.**  The construction lives on the source-normal row.  Ordinary real-axis L2
   still has zero analytic divisor cokernel.
4. **No off-line norm fitting.**  Infinite energy at an off-line point is a theorem from the same
   fixed prime row, not a weight chosen after reading that point.
5. **No scalar-completion overclaim.**  Gamma--Gaussian property-S completion remains neutral
   under dilation.  It can make the row typable, but only `(13)` supplies the source-domain bound.
6. **Generic sources remain a falsifier.**  Translation intervals exist for generic positive
   sources with nonreal Fourier zeros.  Such sources must fail strict descent `(13)`; the
   Euler--Poisson--Gamma theta structure must be used in its proof.
7. **Multiplicity not erased.**  The conjectured closed row must act on the full Jordan tower,
   not just one geometric eigenvector per distinct zero.

## Collision and novelty boundary

All ingredients separately are corpus-known or classical:

- Hedenmalm theta-interval normal multipliers and their two-prime analytic frame;
- prime superspace Wick anisotropy;
- Mertens prime-harmonic and susceptibility asymptotics;
- conditional convergence of `sum_p p^(-1-i x)` for `x!=0`.

The exact termwise identity `(3)` and radial coercivity `(8)` survive as a useful calibration.
The proposed completion and strict-descent route do not survive the corpus audit:

- `prime-valuation-kakutani-polar-third-completion.md` already constructs the nonsummable
  all-prime polar selector and identifies source normality as the RH-bearing gate;
- `prime-aperture-unitary-screen-conjecture.md` and
  `acyclic-finite-fibers-derived-limit-zero.md` rule out manufacturing the missing class from an
  ordinary derived limit of finite acyclic prime packets;
- `adjoint-duality-cauchy-nerve-purity-law.md` already identifies the live replacement as strict
  source cohomology followed by rigged Hodge completion and source-topology resolvent exactness.

The quantum-recurrence paper supplies one additional falsifier: exact relation data is born only
after discontinuous infinite-time completion, but its countable compact recurrence theorem is
continuous only for summable probes.  It explains why finite-time or summable recurrence cannot
prove `(13)`; it does not construct the required strict source comparison.

No external priority claim is made for `(3)`.  The RH route is retired; retaining the exact
identity prevents future candidates from hiding radial susceptibility inside recurrence
language.

## Lean status of positive survivor

`formal/GaloisForLFunctions/RHTower/HedenmalmPrimeNormalWickBoundaryEnergy.lean` formalizes,
unconditionally:

- `norm_sq_complex_sin_eq`;
- `hedenmalmPrimeNormalEnergy_eq_vertical_add_radial`;
- `im_sq_mul_primeClockSusceptibility_le_hedenmalmPrimeNormalEnergy`;
- the sub-`(log X)^2` radial endpoint and its conditional Xi/RH consumer.

It does not formalize the stronger prime-harmonic asymptotic `(7)` or the retired descent claim.

## Gates

- [x] corpus collision audit against prime-clock and Hedenmalm frame cards
- [x] exact Wick decomposition paper proof
- [x] prime-harmonic finite-domain classification paper proof
- [x] root-block RH endpoint isolated
- [x] exact complex-sine/Wick decomposition formalized in Lean
- [x] radial coercivity and sub-log-square endpoint formalized in Lean
- [x] collision with existing Kakutani third completion identified
- [x] recurrence paper classified as limit-order falsifier, not source provider
- [x] strict-descent conjecture retired as an RH-equivalent restatement
- [ ] full prime-harmonic asymptotic `(7)` formalization deferred; not RH-bearing
