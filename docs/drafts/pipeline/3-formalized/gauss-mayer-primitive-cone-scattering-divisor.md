# The primitive-cone source and Mayer scattering divisor

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 1–2.

## Statements

Write the actual positive-unit determinant as `D(w)=A(w)+ζ(w)B(w)`,
where `A=det(I−R(w))` and `B` is the signed constant-projection cofactor.

1. For `Re w>2`, the actual disc-algebra function
   `G_w(z)=1+(z+1)^(−w)+2Σ_(0<p<q, gcd(p,q)=1)(pz+q)^(−w)` satisfies
   `(I−L_w)G_w=1` and `G_w(0)=2ζ(w−1)/ζ(w)`.
2. For `Re w>0`, excluding `w=1,2`,
   `2ζ(w−1)D(w)+ζ(w)B(w)=0` and
   `A(w)=(1+2ζ(w−1))D(w)`.
3. Let `φ(s)` be the actual zero Fourier integral of the raw level-one
   Poincaré series at height one, minus its incoming coefficient one.
   For `Re s>1`, `φ(s)=a(s)ζ(2s−1)/ζ(2s)`, where
   `a(s)=π^(1/2)Γ(s−1/2)/Γ(s)`, and
   `2D(2s)φ(s)+a(s)B(2s)=0`. The independent zeta/Gamma expression
   is meromorphic on the plane. The certified even-word exponential makes
   `D(2s)≠0` in this chamber, so `φ(s)=−a(s)B(2s)/(2D(2s))`.
4. For `0<Re w<1`, the finite analytic multiplicities satisfy
   `ord D=ord B+ord ζ`. Thus `ζ(w)=0` iff `ord B<ord D`.
   Every such zeta zero supplies an actual nonzero disc-algebra vector
   with `L_w f=R(w)f=f`.
5. In the same strip, `D=0` iff `ζ(w)=0` or `B=0`; and `A=0` iff
   `ζ(w)=0`, `B=0`, or `ζ(w−1)=−1/2`. These causes may overlap.

All five statements are Lean-certified.

## Proof

**Actual source.** Branch `n` maps a primitive pair `(p,q)` to `(q,nq+p)`.
Euclidean division gives a unique predecessor whenever the new first
coordinate is at least two; coprimality excludes zero remainder. The
remaining rows have first coordinate one. If `H` is the cone sum,
`U=(1+z)^(−w)`, and `C` the sum of these boundary rows, this partition gives
`L_wH=H−C`, `L_w1=U+C`, and `L_wU=C`. The last equality also follows from
the exact successor response `L_w(1−U)=U`. Hence
`L_w(1+U+2H)=U+2H`.

On the whole Mayer disc, write `(p,q)=(i+1,i+j+2)` and use
`Re(pz+q)≥3/2+i/2+j`. The uniform power bound is
`exp(π|Im w|)(3/2+i/2+j)^(−Re w)`, a summable Barnes cone majorant.
Principal logarithms on the right half-plane justify the exact branch
power identities. At zero, grouping by height `q` gives `φ(q)` terms;
the totient Dirichlet series is `ζ(w−1)/ζ(w)`.

**Cofactor.** Transfer `G_w` through the actual Cauchy Hilbert realization.
The rank-one determinant update for `I−L_w+tP`, using the supplied
response `tG_w`, gives `D(w)(1+tG_w(0))`; its regularized trace
exponential cancels the diagonal correction. Affine dependence on the
constant mode also gives `D(w)−tB(w)`. Thus `B=−DG_w(0)`, without an
inverse premise, proving the scalar identity in `Re w>2`.

**Continuation.** Let `Z` be the entire continuation of `(w−1)ζ(w)`,
with `Z(1)=1`. Set
`N=(w−1)A+Z(w)B` and
`H=2Z(w−1)N+(w−2)Z(w)B`.
Both are holomorphic on `Re w>0`. The absolute-chamber identity makes
`H=0` there, so connectedness and the identity theorem give `H=0`
throughout the half-plane. Outside `w=1,2`, cancel `(w−1)(w−2)`.
The factorization of `A` follows from `D=A+ζB`.

**Independent normalization.** Actual Poincaré Fourier extraction gives
`φ(s)=𝓕(CauchyPowerKernel)(0)ζ(2s−1)/ζ(2s)` at height one.
The zero-frequency transform is
`π^sΓ(s−1/2)π^(−s+1/2)/Γ(s)=a(s)`.
This fixes the scattering convention independently of `D`.

**Multiplicity.** The functional equation and Euler-product nonvanishing
show `ζ(w−1)≠0` throughout `0<Re w<1`. Hence locally
`D=ζB·[−1/(2ζ(w−1))]`, with the bracket a holomorphic unit.
The cofactor is holomorphic on the connected source half-plane and
`B(1)≠0`, so its order is finite everywhere. The entire function `Z`,
nonzero at one, similarly excludes infinite zeta order. Orders add,
and the two factorizations give the exact zero classifications.
Fredholm's actual disc-algebra eigenvector theorem supplies `L_wf=f`
at a determinant zero; at `ζ(w)=0`, `L_w=R(w)`.

## Lean certificates

All modules lie in `GaloisForLFunctions/RenormalizedIntersectionTheory/`.

| Module | Main declarations | Status |
|---|---|---|
| `GaussMayerCoprimeRenewal` | `renewalEquiv`, `boundaryDeepEquiv` | Certified |
| `GaussMayerCoprimeSource` | `summable_norm_term`, `green_response` | Certified |
| `GaussMayerCoprimeHeight` | `green_zero` | Certified |
| `GaussMayerCoprimeCofactor` | `determinant_shift`, `polePart_eq_response` | Certified |
| `GaussMayerCofactorContinuation` | `clearedIdentity_zero`, `zeta_cofactor_identity`, `regularPart_eq_shifted_zeta_factor` | Certified |
| `GaussMayerScatteringNormalization` | `actualScattering_eq`, `actual_cofactor_identity`, `meromorphic_scatteringEntry` | Certified |
| `GaussMayerScatteringMultiplicity` | `determinant_orderNat`, `zeta_zero_iff_excess_order`, `regularPart_zero_iff`, `remainder_eigenfunction_of_zeta_zero` | Certified |

Certified modules passed direct production checks and transitive axiom
audits using only `propext`, `Classical.choice`, and `Quot.sound`.

## Boundary

No cofactor-zero exclusion or shifted-level-set exclusion in the strip
is asserted. The relative-order criterion cancels common zeros;
a totalized quotient at a common zero cannot replace it.
Negative-unit constant-mode cancellation holds throughout the complex
source half-plane, while certified negative-unit nonvanishing applies
only to positive real source parameters. No Krein separation, spectral
gap, or resonance exclusion follows from these identities alone.
