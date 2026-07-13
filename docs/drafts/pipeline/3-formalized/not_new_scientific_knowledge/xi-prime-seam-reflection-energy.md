# Xi prime-seam energy is a horizontal prime-zeta reflection distance

- **ID:** `xi-prime-seam-reflection-energy`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[FORMALIZATION]`, `[VALUE RELATION]`, `[TOP-DOWN QUANTITATIVE BRIDGE]`
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamReflectionEnergy.lean`
- **Parents:** `xi-prime-seam-pair-asymptotics.md`; `xi-prime-seam-pair-variance.md`

## Statement

For an open-strip point `rho` and a rational prime `p`, put

```text
C_p(rho)=log(p)(p^(-conj(rho))-p^(-(1-rho))).
```

Lean proves the exact value relation

```text
|C_p(rho)|^2/p
 =log(p)^2[
    p^(-(1+2 Re(rho)))
   +p^(-(3-2 Re(rho)))
   -2p^(-2)].                                               (1)
```

Equivalently,

```text
|C_p(rho)|^2/p
 =4log(p)^2 p^(-2)
    sinh((Re(rho)-1/2)log(p))^2.                            (2)
```

Thus every summand, and hence the full energy

```text
S(rho)=sum_p |C_p(rho)|^2/p,                                (3)
```

is independent of `Im(rho)` and invariant under functional-equation reflection
`rho -> 1-conj(rho)`.

Define the prime logarithmic moment curve

```text
K(beta)=sum_p log(p)^2 p^(-beta),       beta>1.              (4)
```

Then

```text
S(rho)
 =K(1+2 Re(rho))+K(3-2 Re(rho))-2K(2).                      (5)
```

The prime-two coordinate gives the quantitative coercivity law

```text
(Re(rho)-1/2)^2 log(2)^4 <= S(rho).                         (6)
```

Finally, if `E_F(rho)` is the reciprocal-prime pair energy and
`M_F=sum_(p in F)1/p`, then the already formalized cofinal limit becomes

```text
E_F(rho)/M_F
 ->2[K(1+2 Re(rho))+K(3-2 Re(rho))-2K(2)].                 (7)
```

## Prime-zeta/RKHS interpretation

For the prime zeta function `P(beta)=sum_p p^(-beta)` on `beta>1`, termwise differentiation gives
`K=P''`.  Hence `(5)` is a centered symmetric second difference of `P''` about `2`.

More geometrically, define the prime feature

```text
Phi(s)_p=log(p)p^(-s)/sqrt(p).                              (8)
```

For `Re(s),Re(w)>0`, its Gram kernel is

```text
<Phi(s),Phi(w)>=P''(1+conj(s)+w).                           (9)
```

Taking `s=conj(rho)` and `w=1-rho` gives

```text
S(rho)=||Phi(conj(rho))-Phi(1-rho)||^2.                    (10)
```

Equation `(5)` is therefore a squared Hilbert distance between the Schwarz and FE endpoints, not
only an algebraic convexity identity.  It is a static constraint geometry: no translation flow or
zero ordering is involved.

## Top-down consequence

The two-particle Sonin route now has a quantitative endpoint.  Any source theorem proving

```text
E_F(rho)/M_F <= epsilon_F,      epsilon_F -> 0,             (11)
```

on an actual Xi divisor fibre gives, by `(6)`--`(7)`,

```text
|Re(rho)-1/2|^2
 <= epsilon_F/(2 log(2)^4)+o(1),                            (12)
```

and therefore forces that fibre onto the critical line.  The required Sonin Calkin hypothesis is
only sub-root reciprocal-prime-mass growth, not a uniform bound.

The height cancellation in `(1)` is also a route-selection fact.  Any proposed source estimate for
this coefficient may be reduced to horizontal reflection geometry; oscillatory cancellation in
`Im(rho)log(p)` cannot be the missing mechanism because it has already disappeared exactly.

## Literature boundary

Fröberg's classical work on the prime zeta function is the parent for `P` and its analytic
continuation.  The differentiation identity `P''(beta)=sum_p log(p)^2p^(-beta)` on `beta>1`, the
feature realization `(9)`, and the centered-distance algebra are standard Dirichlet-series/RKHS
calculus.  No scientific novelty is claimed for `(1)`--`(10)`.

Connes--Consani's
[*Quasi-inner functions and local factors*](https://arxiv.org/abs/2008.10974) proves compactness of
the Hardy off-diagonal corner for every finite archimedean-compensated local-factor product, while
individual nonarchimedean factors are not quasi-inner.  This is adjacent source geometry but does
not prove `(11)`: the ordinary all-place completed ratio regularizes to `1`, and the present corpus
proves finite additive Euler directions remain Calkin-independent.

Connes--Consani--Moscovici's
[*Zeta zeros and prolate wave operators*](https://arxiv.org/abs/2310.18423) provides the stable
semilocal Sonin/prolate framework, but no theorem matching the horizontal prime-feature distance
`(10)` to a cofinally sub-root source section was located.

`[OPEN CORE]` Construct, before the completed local-ratio product collapses, a source-defined
second-order/relative Sonin section whose principal Calkin coefficient is the endpoint distance
`Phi(conj(rho))-Phi(1-rho)`, and prove sub-root reciprocal-prime-mass growth without Xi zero-location
input.  Finite quasi-inner compactness alone supplies neither this coefficient identification nor
the cofinal rate.

## Principal declarations

```text
orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_reflectionSecondDifference
orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_of_re_eq
orbitwisePrimeSeamWeightedNormSq_eq_of_re_eq
orbitwisePrimeSeamWeightedNormSq_one_sub_star
primeLogHilbertFeature
primeLogHilbertFeature_reflectionDifference
norm_sq_primeLogHilbertFeature_reflectionDifference
primeLogHilbertReflectionDistanceSq
primeLogHilbertReflectionDistanceSq_eq_orbitwisePrimeSeamWeightedNormSq
primeLogSquareMoment
summable_primeLogSquareMoment
orbitwisePrimeSeamWeightedNormSq_eq_primeLogSquareMoment_secondDifference
primeTwo_reflectionSecondDifference_le_orbitwisePrimeSeamWeightedNormSq
orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_sinh
horizontalDisplacement_sq_mul_log_two_pow_four_le_orbitwisePrimeSeamWeightedNormSq
tendsto_orbitwisePrimeSeamPairEnergy_div_mass_to_primeLogSquareMoment_secondDifference
```

## Gates

- [x] exact per-prime reflection second difference
- [x] exact hyperbolic-square formula
- [x] height independence
- [x] FE-reflection invariance
- [x] full prime-moment second difference
- [x] prime-two lower bound
- [x] explicit quadratic horizontal coercivity
- [x] normalized pair-energy curvature limit
- [x] Lean proof and axiom audit
- [ ] source-defined relative Sonin realization of the endpoint feature difference
- [ ] cofinal sub-root Calkin growth
