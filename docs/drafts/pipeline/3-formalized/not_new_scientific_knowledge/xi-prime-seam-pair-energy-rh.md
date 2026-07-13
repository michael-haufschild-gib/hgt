# Xi prime-seam reciprocal pair energy criterion

- **ID:** `xi-prime-seam-pair-energy-rh`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[FORMALIZATION]`, `[BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/sonin-two-particle-prime-coherence.md`
- **Endpoint parent:** `xi-prime-seam-coherence-collapse.md`
- **Value-relation continuation:** `xi-prime-seam-pair-variance.md`
- **Asymptotic continuation:** `xi-prime-seam-pair-asymptotics.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamPairEnergy.lean`

## Statement

For a prime-indexed complex potential `a_p` and a finite set of primes `F`, define the ordered
reciprocal-prime pair energy

```text
E_F(a)=sum_(p in F) sum_(q in F) |a_p-a_q|^2/(p q).       (1)
```

Then

```text
sup_(F finite) E_F(a)<infinity
  iff
a_p is constant on the primes.                            (2)
```

For an open-strip point `rho`, specialize to the canonical FE--Schwarz seam potential

```text
a_p(rho)=log(p)(p^(-conj(rho))-p^(-(1-rho))).              (3)
```

The exact fiberwise law is

```text
sup_(F finite) E_F(a(rho))<infinity
  iff
Re(rho)=1/2.                                               (4)
```

Consequently, bounded pair energy on every Xi divisor fibre is equivalent to the Riemann
hypothesis.  The contradiction form is also formalized:

```text
not RH
  -> exists rho in the Xi divisor,
       forall B, exists finite F, B<E_F(a(rho)).            (5)
```

Thus false RH produces not merely a nonzero seam but arbitrarily large finite two-particle
reciprocal-prime energy on one actual divisor fibre.

## Proof

Assume all finite pair energies are bounded by `B`.  Fix primes `p,r`.  For every prime `q`,

```text
|a_p-a_r|^2 <= 2|a_p-a_q|^2+2|a_r-a_q|^2.                 (6)
```

After multiplying by `1/q` and summing over a finite prime set `S`, the two rows on the right are
bounded by `pB` and `rB`, respectively.  Hence

```text
|a_p-a_r|^2 sum_(q in S) 1/q <= 2(p+r)B.                  (7)
```

Euler's divergence of the reciprocal-prime series forces `a_p=a_r`.  Since `p,r` were arbitrary,
the potential is constant.  The converse has zero pair energy.

For `(3)`, constant prime potentials vanish because the seam tends to zero along cofinal primes.
The prime-two seam vanishes exactly when `Re(rho)=1/2`.  This proves `(4)`.  Applying `(4)` on
every Xi divisor fibre and using functional-equation symmetry proves the global equivalence.

## Positive no-go and surviving source target

The result converts the two-particle Calkin route's no-go into an exact positive target:

```text
construct source-defined finite operators T_F(rho)
  -> prove a uniform Calkin upper bound for T_F(rho)
  -> use the paper-proven Sonin tensor-square lower estimate
       E_F(a(rho)) <= 2 dist(T_F(rho), Compact)^2
  -> bounded pair energy
  -> prime coherence and cofinal seam collapse
  -> RH.                                                    (8)
```

The factor `2` is only the conversion from the unordered `p<q` energy in the paper theorem to the
ordered energy `(1)` used by the Lean endpoint.

The new theorem closes the arithmetic infinite-prime and RH endpoints of `(8)`.  It does not
construct `T_F(rho)` or prove its uniform source-side Calkin bound.  Assuming that bound would
still be circular unless the operators are built from the prime--Gamma/Sonin source without
using Xi zero locations.

The continuation `XiPrimeSeamPairVariance.lean` now proves the exact factorization

```text
E_F(a)=2(sum_(p in F)1/p)(sum_(p in F)|a_p|^2/p)
       -2|sum_(p in F)a_p/p|^2.
```

Thus the finite pair energy is a one-particle weighted variance with one rank-one mean removed.
This reduces the prospective source construction from arbitrary pairwise coefficient control to a
mass-amplified one-particle seam norm plus a rank-one channel; it does not itself supply the missing
operator upper bound.

The asymptotic continuation proves more: if `M_F=sum_(p in F)1/p`, then

```text
E_F(rho)/M_F -> 2 sum_p |a_p(rho)|^2/p,
```

with a strictly positive limit at every off-line strip point.  Therefore a uniform Calkin upper
bound is unnecessary.  The paper lower estimate closes the route from the weaker source target
`dist(T_F(rho),Compact)=o(sqrt(M_F))`.

## Literature audit

`[SEARCH]` Connes--Moscovici's
[*Prolate spheroidal operator and Zeta*](https://arxiv.org/abs/2112.05500) supplies the actual
archimedean Sonin carrier and identifies its negative prolate spectrum with the ultraviolet
zeta-zero counting law.  It does not contain a tensor-square coefficient-recovery estimate or an
all-prime reciprocal pair-energy bound.

`[SEARCH]` Connes--Consani--Moscovici's
[*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423) constructs stable
semilocal Sonin spaces and a semilocal prolate candidate.  The paper presents semilocal Weil
positivity as the prospective completion and explicitly leaves a further prolate candidate to
future work; it does not construct the source-defined operators `T_F(rho)` in `(8)`.

`[SEARCH]` Connes--Consani's
[*Weil positivity and Trace formula, the archimedean place*](https://arxiv.org/abs/2006.13771)
proves the one-place positive compression mechanism and states that its ingredients extend to the
general semilocal setting where Weil positivity would imply RH.  This supports the carrier choice,
but supplies neither the prime-pair potential map nor the uniform Calkin upper estimate.

`[POSITIVE NO-GO]` In
[*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368), Connes--Consani prove that the direct
local-inner-function argument fails: the finite-prime and archimedean local-factor ratios have
unit boundary modulus but are not bounded inner functions, and the proposed local inequality is
false in general.  Positively, a viable construction must retain the global Poisson normalization
and the two Weil moment constraints; a tensor product of independent local contractions cannot be
the missing source upper bound.

`[SEARCH]` Ramis--Richard-Jung--Thomann's 2025
[*New eigenfunctions for the negative part of the Connes--Moscovici prolate spectrum*](https://doi.org/10.5802/crmath.780)
proves negativity and gives order-at-most-`1/2` spectral determinants for the nonclassical
archimedean prolate spectrum.  This strengthens the trace-class resolvent control used elsewhere
in the pipeline, but it does not address semilocal prime-pair Calkin control.

`[OPEN CORE]` No located primary source supplies the exact missing implication in `(8)`.  The
literature narrows its permissible form: it must be a globally normalized, source-pointed
semilocal construction that retains pair differences before scalarization.  A placewise inner
multiplier, an ultraviolet spectral match, or a transported archimedean prolate operator is
insufficient.

## Lean realization

Principal declarations:

```text
primePairDifferenceRow
primePairDifferenceEnergy
PrimePairDifferenceEnergyBounded
primePairDifference_eq_of_energyBounded
primePairDifferenceEnergyBounded_iff_constant
OrbitwisePrimeSeamPairEnergyBounded
orbitwisePrimeSeamPairEnergyBounded_iff_re_eq_half
orbitwisePrimeSeamPairEnergy_unbounded_of_re_ne_half
XiPrimeSeamPairEnergyBounded
xiPrimeSeamPairEnergyBounded_iff_riemannHypothesis
exists_xiPrimeSeamPairEnergy_unbounded_of_not_riemannHypothesis
```

The proof uses only the existing reciprocal-prime divergence theorem and the formalized seam
coherence-collapse endpoint.  It contains no placeholder axiom or numerical input.

## Gates

- [x] abstract bounded pair energy implies constant prime potential
- [x] constant potential implies zero pair energy
- [x] canonical prime seam substituted without divisor-dependent source data
- [x] fiberwise bounded-energy/critical-line equivalence
- [x] global bounded-energy/RH equivalence
- [x] false-RH unbounded-energy contradiction form
- [x] exact finite rank-one weighted-variance factorization
- [x] Lean proof
- [ ] source-defined two-particle Sonin operator attached to `(3)`
- [ ] sub-root reciprocal-mass Calkin growth for that operator
- [ ] complete RH proof
