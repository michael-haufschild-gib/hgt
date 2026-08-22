# Heat-aperture prime tail / seam reflection collapse

- **ID:** `heat-aperture-prime-seam-reflection-collapse`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean source drafted and wired, verification deferred
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The FE--Schwarz difference of every prime coefficient in the canonical
  heat-aperture Euler-log tail is exactly the corresponding canonical prime seam divided by the
  nonzero factor `log p`.  The whole reflected prime family is therefore fixed if and only if its
  scale-two member is fixed, equivalently if and only if the parameter lies on the critical line.

## Exact value relation

Write the canonical heat-aperture prime-power coefficient as

```text
c_N(s)=[Lambda(N)/log N] N^(conj(s)-1).
```

For a prime `p`, the Euler-log coefficient is one, so

```text
c_p(s)=p^(conj(s)-1).                                  (1)
```

At the functional-equation and Schwarz images of an arbitrary complex parameter `rho`, equation
`(1)` gives

```text
c_p(1-rho)=p^(-conj(rho)),
c_p(conj(rho))=p^(-(1-rho)).                           (2)
```

Consequently

```text
log(p)[c_p(1-rho)-c_p(conj(rho))]
  =log(p)[p^(-conj(rho))-p^(-(1-rho))]
  =C_p(rho),                                           (3)
```

where `C_p` is the canonical FE--Schwarz prime seam already used by the Hurwitz orientation and
two-particle Sonin chains.

Equation `(3)` is pointwise and uses neither an Xi-zero hypothesis nor an open-strip hypothesis.
It is an equality of source coordinates, not an asymptotic analogy.

## First-coefficient collapse

The existing seam faithfulness theorem says

```text
C_2(rho)=0 iff Re(rho)=1/2.                            (4)
```

Since `log 2` is nonzero, `(3)` and `(4)` imply

```text
c_2(1-rho)=c_2(conj(rho))
  iff Re(rho)=1/2.                                     (5)
```

If `Re(rho)=1/2`, then `conj(rho)=1-rho`, so every coefficient agrees.  Therefore

```text
[for every prime p, c_p(1-rho)=c_p(conj(rho))]
  iff c_2(1-rho)=c_2(conj(rho))
  iff Re(rho)=1/2.                                     (6)
```

The same conclusion holds if the left side is strengthened to every integer coefficient: on the
critical line the two parameter arguments are literally equal, while the scale-two member already
forces the line.

## Actual semilocal connection factorization

Let the genuine degree-one local Euler connection value be

```text
Phi_p(s)=log(p) p^(-s)/(1-p^(-s)).                      (6a)
```

Throughout the open critical strip, both Euler denominators below are nonzero.  A direct rational
identity gives

```text
Phi_p(conj(rho))-Phi_p(1-rho)
 =C_p(rho)/[(1-p^(-conj(rho)))(1-p^(-(1-rho)))].        (6b)
```

Thus the common charge is not merely the first derivative of an empty Euler-parameter chart.  It
is also, up to an explicit invertible factor, the difference of two actual semilocal connection
values.  At `p=2`,

```text
Phi_2(conj(rho))=Phi_2(1-rho)
  iff c_2(1-rho)=c_2(conj(rho))
  iff Re(rho)=1/2.                                     (6c)
```

Equation `(6b)` is the useful positive reformulation of the earlier normalization problem: a
source theorem need not separately prove that an abstract common constant is zero.  It may instead
prove equality of the two concrete Euler connection values.  No theorem presently forces this
equality on every Xi fibre, so `(6b)` is an interface improvement rather than a discharge of the
orientation input.

## Actual Euler-point tangent factorization

The literal Euler-parameter tangent at the actual point `a_p=1` is

```text
T_p(s)=log(p) p^(-s)/(1-p^(-s))^2.                       (6d)
```

Put `q=p^(-conj(rho))` and `r=p^(-(1-rho))`.  Direct expansion gives the exact identity

```text
T_p(conj(rho))-T_p(1-rho)
 =C_p(rho) (1-q r)/[(1-q)^2(1-r)^2].                    (6e)
```

Indeed,

```text
q(1-r)^2-r(1-q)^2=(q-r)(1-q r).                         (6f)
```

In the open critical strip, `|q|<1` and `|r|<1`.  Hence neither Euler denominator nor the cross
factor `1-q r` can vanish.  Moreover, every individual prime seam is faithful:

```text
C_p(rho)=0 iff Re(rho)=1/2                              (6g)
```

for every prime `p`, not only for `p=2`.  Combining `(6e)` and `(6g)` yields

```text
T_p(conj(rho))=T_p(1-rho) iff Re(rho)=1/2.              (6h)
```

This is a genuine interface reduction.  Any source construction already formulated at the actual
Euler point may target one finite tangent equality directly.  It need not move to `a_p=0`, extract
the degree-one coefficient, control the higher Lambert grades, or pass to all primes.  The prime
may be chosen to match the finite place accessible to the operator construction.

The reduction is local to the scalar FE--Schwarz value interface.  It does not erase the
higher-grade principal tail in the separate Sonin exterior-Calkin route, where one must transfer
an actual operator section to an empty-parameter coefficient with a quantitative quotient norm.
Nor does it prove `(6h)` on Xi fibres: a source theorem producing the graded-reality equality is
still required.

### Koebe-coordinate interpretation

The rational map in `(6d)` is not an ad hoc Euler expression.  If

```text
k(q)=q/(1-q)^2,
```

then `k` is the classical Koebe function and

```text
T_p(s)=log(p) k(p^(-s)).                                 (6i)
```

The global rational identity

```text
k(q^(-1))=k(q)                                          (6j)
```

explains the cross factor in `(6e)`: the only algebraic collision is the reciprocal pair.  The
Koebe function is univalent on the unit disk, while both open-strip Euler characters `q` and `r`
lie strictly inside that disk.  Hence the reciprocal collision lies outside the admissible source
chamber and equality of the Koebe values forces `q=r`.

This supplies the right parent theory for `(6e)`--`(6h)`: it is a static univalent-coordinate
constraint, not a hidden evolution equation.  Classical and recent geometric-function treatments
use precisely `q/(1-q)^2` as the Koebe function; see S. L. Krushkal,
[*Extremality of Koebe's Function*](https://doi.org/10.3390/axioms14120873).  The identification
does not make the Xi-fibre equality automatic, and no Loewner-flow construction is inferred from
it.

### Spectral curvature and trigamma reflection

The same actual-point tangent is already the spectral curvature of the genuine semilocal
connection.  Differentiating `(6a)` in `s` gives

```text
Phi_p'(s)=-log(p) T_p(s).                                (6k)
```

Thus the any-one-prime criterion `(6h)` is equivalently

```text
Phi_p'(conj(rho))=Phi_p'(1-rho) iff Re(rho)=1/2.         (6l)
```

This matters for the operator interface: a normal-curvature reader need not be recast as an
Euler-parameter Hessian.  If it returns equality of the spectral connection derivatives at the
two reflected fibre points, `(6k)` transfers that value directly to `(6h)`.

There is also an exact Gamma coordinate.  With

```text
u_p(s)=i log(p) s/(2 pi),
```

the trigamma reflection formula and `sin(iw)=i sinh(w)` give

```text
T_p(s)=-log(p)/(4 pi^2)
  [psi'(u_p(s))+psi'(1-u_p(s))].                         (6m)
```

Hence the actual Euler tangent is the imaginary-slope trigamma-reflection curvature of the
reciprocal-Gamma pair already representing the local Euler factor.  This splices three existing
corpus layers without approximation:

```text
semilocal spectral connection curvature
  = actual Euler-parameter tangent
  = imaginary-slope trigamma-reflection curvature.       (6n)
```

`PolygammaReflection.lean` already formalizes the general trigamma reflection identity, while
`finite-euler-imaginary-gamma-reflection-weld.md` proves the local Euler/Gamma substitution on
paper.  The direct spectral derivative equality `(6k)` is drafted in the present Lean module.
The substitution `(6m)` remains paper-level.  Neither identity supplies the missing Xi-fibre
graded-reality theorem, but a future source reader may now land in any of the three native
coordinates in `(6n)`.

## Top-down consequence

The previously separate-looking right ends

```text
reflected heat-aperture prime-tail equality,
first-prime seam vanishing,
FE--Schwarz Hurwitz pair dependence,
zero Xi--Hurwitz orientation energy
```

are coordinates on the same orientation defect.  In particular, a proof that first establishes
reflection equality for the entire infinite heat tail is overpowered: only the exact finite value
relation at `N=2` is needed.

Over the Xi divisor, the existing formal endpoints splice `(6)` into

```text
source-core prime--Gamma positivity
  -> zero orientation energy
  -> C_2(rho)=0 for every Xi divisor point
  <-> c_2(1-rho)=c_2(conj(rho)) for every Xi divisor point
  -> RH.                                               (7)
```

This does not discharge the source-core positivity input.  It identifies the common-charge
normalization as a concrete finite coefficient equality and proves that no additional all-tail
compatibility theorem is required.

## Literature and parent-theory boundary

The ingredients in `(1)`--`(3)` are classical Euler-log coefficient algebra and the zeta
functional-equation/Schwarz reflection pair.  Burnol's explicit-formula and conductor-operator
framework and the Connes--Consani Sonin compression provide parent settings for prime--Gamma and
archimedean positivity, but they do not supply the missing equality in `(7)` on Xi fibres.  The
present claim is therefore classified as a project bridge, not as new scientific knowledge.

## Lean surface

The unverified source draft is

```text
formal/GaloisForLFunctions/RHTower/HeatAperturePrimeSeamReflection.lean
```

with declarations

- `heatAperturePrimePowerCoeff_prime`;
- `log_mul_heatAperturePrimePowerCoeff_FE_sub_Schwarz_eq_seam`;
- `heatAperturePrimeTwoCoeff_FE_eq_Schwarz_iff_re_eq_half`;
- `heatAperturePrimeCoefficientsFESchwarzFixed_iff_re_eq_half`;
- `heatAperturePrimeCoefficientsFESchwarzFixed_iff_primeTwo`;
- `degreeOneEulerLocalFlux_Schwarz_sub_FE_mul_denominators_eq_seam`;
- `degreeOneEulerLocalFlux_primeTwo_Schwarz_eq_FE_iff_re_eq_half`;
- `degreeOneEulerLocalFlux_Schwarz_eq_FE_iff_heatPrimeTwoCoeff_eq`;
- `hasDerivAt_degreeOneEulerLocalFlux_spectral`;
- `primeEulerUnitTangent_Schwarz_sub_FE_mul_denominator_sq_eq_seam_mul_cross`;
- `orbitwiseNatPrimeSeamCharge_eq_zero_iff_re_eq_half`;
- `heatAperturePrimeCoeff_FE_eq_Schwarz_iff_re_eq_half`;
- `degreeOneEulerLocalFlux_Schwarz_eq_FE_iff_re_eq_half`;
- `one_sub_prime_FESchwarz_character_product_ne_zero`;
- `primeEulerUnitTangent_Schwarz_eq_FE_iff_re_eq_half`;
- `degreeOneEulerLocalFlux_spectralDeriv_Schwarz_eq_FE_iff_re_eq_half`;
- `primeEulerUnitTangent_Schwarz_eq_FE_iff_degreeOneEulerLocalFlux_Schwarz_eq_FE`;
- `primeEulerUnitTangent_Schwarz_eq_FE_iff_heatAperturePrimeCoeff_eq`;
- `primeEulerUnitTangent_two_Schwarz_eq_FE_iff_heatPrimeTwoCoeff_eq`.

It is imported by `formal/GaloisForLFunctions/RHTower.lean`.  Targeted verification on 2026-08-22
passed: `lake env lean GaloisForLFunctions/RHTower/HeatAperturePrimeSeamReflection.lean` and
`lake build GaloisForLFunctions.RHTower.HeatAperturePrimeSeamReflection`.  Stage 3 promotion
remains pending the source-core prime--Gamma positivity theorem.

## Gates

- [x] exact coefficient/seam identity proved on paper
- [x] whole-family-to-prime-two collapse proved on paper
- [x] actual Euler-connection/seam factorization proved on paper
- [x] actual Euler-point tangent/seam factorization proved on paper
- [x] any-one-prime tangent equality reduced to the critical line
- [x] any-one-prime heat/connection/tangent coordinate triangle proved on paper
- [x] actual tangent identified with normalized spectral connection curvature
- [x] actual tangent identified on paper with imaginary-slope trigamma reflection curvature
- [x] source draft added and imported by the RHTower umbrella
- [x] classified as a bridge rather than an independent RH producer
- [x] targeted Lean verification (2026-08-22; direct Lean and focused module build)
- [ ] source-core prime--Gamma positivity
