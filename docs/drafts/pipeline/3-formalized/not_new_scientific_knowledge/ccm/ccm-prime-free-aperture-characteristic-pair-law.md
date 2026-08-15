# The prime-free CCM aperture already has a real characteristic pair

- **ID:** `ccm-prime-free-aperture-characteristic-pair-law`
- **Stage:** 3-formalized (paper proof; Lean certificate alongside)
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the exact corrected CCM symbol, the classical value of `digamma(1/4)`, and the
  intermediate value theorem

## Statement

Put

```text
m(xi)=Re psi(1/4+i xi/2)-log pi,
m_0=m(0)=psi(1/4)-log pi,

P_a(xi)
 =[2sinh(a)cos(2a xi)+4xi cosh(a)sin(2a xi)]/(xi^2+1/4),

W_a(xi)=m(xi)
 -2 sum_(2<=n<=exp(2a))Lambda(n)n^(-1/2)cos(xi log n)
 +P_a(xi).                                                 (1)
```

Define the explicit positive aperture

```text
a_0=min((log 2)/2, arsinh(-m_0/8)).                         (2)
```

Then `a_0>0`, and for every `0<a<a_0` the real characteristic set of `W_a` contains a nonzero
symmetric pair:

```text
there exists tau_a>0 such that
W_a(tau_a)=W_a(-tau_a)=0.                                  (3)
```

Thus the zero-free scalar Wiener--Hopf branch is false already in the first, prime-power-free CCM
aperture.

## Proof

The classical quarter-value identity is

```text
psi(1/4)=-gamma-pi/2-3log 2.                               (4)
```

Therefore

```text
m_0=-gamma-pi/2-3log 2-log pi<0,                           (5)
```

so `arsinh(-m_0/8)>0` and hence `a_0>0`.

If `0<a<(log 2)/2`, then `exp(2a)<2`; the finite prime-power sum in `(1)` is empty. The exact polar
value is

```text
P_a(0)=8sinh(a).                                          (6)
```

If also `a<arsinh(-m_0/8)`, strict monotonicity of `sinh` gives

```text
W_a(0)=m_0+8sinh(a)<0.                                    (7)
```

For fixed aperture, the corrected symbol is continuous, real, even, and satisfies

```text
W_a(xi)=log|xi|+O_a(1)->+infinity                         (8)
```

as `|xi|->infinity`. Choose `R>0` with `W_a(R)>0`. The intermediate value theorem applied on
`[0,R]` gives `tau_a in (0,R)` with `W_a(tau_a)=0`; evenness gives the zero at `-tau_a`. `QED`

## Positive CCM consequence

Suzuki--Yoshida prove that the restricted Weil form is positive and the compact screw operator is
injective for all sufficiently small apertures. Combining that fact with `(3)` shows:

```text
real zeros of the ambient corrected symbol
  do not produce screw null vectors by themselves;
the exterior trace, hard support seam, mean-zero condition,
and two affine anchors eliminate the characteristic modes. (9)
```

Accordingly, every successful finite-interval factorization is forced into the characteristic
Evans branch even at the initial aperture. It must retain

```text
the symmetric real characteristic packet
  + the inverse zero-free multiplier
  + the exterior trace
  + two-sided compact support
  + mean zero
  + the two lost-affine-mode anchors.                      (10)
```

A proof based on `W_a` having no real zeros cannot establish CCM injectivity. More strongly, any
factorization discarding the exterior trace contradicts the coexistence of `(3)` with known
small-aperture injectivity.

## Classification and Lean decision

The proof uses the classical digamma quarter value, the exact already-formalized polar multiplier,
and the intermediate value theorem. It is a route-selection bridge, not new scientific knowledge.
The current Lean tree formalizes `(6)` but does not define the full real symbol, its digamma
asymptotic, or its finite prime cutoff. Formalizing only the scalar inequality in `(7)` would not
certify the characteristic-pair theorem, so no wrapper-only Lean module is added.

## Gates

- [x] explicit prime-free aperture found
- [x] corrected zero-frequency symbol proved negative there
- [x] positive-frequency characteristic zero forced
- [x] symmetric characteristic pair forced
- [x] zero-free scalar factorization branch retired at the initial aperture
- [ ] construct the source-defined exterior-trace Evans relation
- [ ] prove that relation remains injective through every prime-entry aperture
- [ ] RH


## Lean status

**Formalized unconditionally, 2026-08-15**, in
`formal/GaloisForLFunctions/RHTower/CCMPrimeFreeApertureCharacteristicPair.lean`.  The earlier
decision ("the current Lean tree ... does not define the full real symbol, its digamma asymptotic, or
its finite prime cutoff") is out of date on all three counts: the tree owns Gauss's quarter value
(`RHTower/DigammaQuarter.lean`), the vertical logarithmic coercivity of `Re psi`
(`RHTower/DigammaVerticalLogGrowth.lean`), and digamma continuity on the right half-plane
(`RHTower/ArchEnvelope.lean`).

- `ccmArchSymbol`, `ccmPolarMultiplier`, `ccmPrimeCutoffSum`, `ccmCorrectedSymbol` — equation `(1)`,
  the full real symbol including the finite prime cutoff `Finset.Icc 2 ⌊exp(2a)⌋₊`.
- `ccmPrimeFreeAperture` — equation `(2)`; **`ccmPrimeFreeAperture_pos`** is `a_0 > 0`, using
  `archRatioCharge_pos` and strict monotonicity of `sinh`.
- **`ccmArchSymbol_zero`**, **`ccmArchSymbol_zero_neg`** — equations `(4)`--`(5)`:
  `m_0 = psi(1/4) - log pi = -archRatioCharge < 0`, from Gauss's quarter value.
- **`ccmPolarMultiplier_zero`** — equation `(6)`, `P_a(0) = 8 sinh a`.
- **`ccmPrimeCutoffSum_eq_zero`** — the prime-free statement: below `(log 2)/2` the cutoff index set
  `Icc 2 ⌊exp(2a)⌋₊` is empty.
- **`ccmCorrectedSymbol_zero_neg`** — equation `(7)`.
- **`ccmArchSymbol_even`**, `ccmPolarMultiplier_even`, `ccmPrimeCutoffSum_even`,
  **`ccmCorrectedSymbol_even`** — evenness, the archimedean half through `digamma_conj`.
- `continuous_ccmArchSymbol`, `continuous_ccmPolarMultiplier`, `continuous_ccmPrimeCutoffSum`,
  **`continuous_ccmCorrectedSymbol`** — continuity of the symbol in the frequency.
- **`ccmArchSymbol_ge`**, **`tendsto_ccmArchSymbol_atTop`** — equation `(8)`: the archimedean part
  is bounded below by `log(2 + |ξ/2|)` minus an explicit constant, hence tends to `+∞`.
- **`abs_ccmPolarMultiplier_le`** — a *uniform* bound `|P_a| ≤ 8|sinh a| + 4 cosh a`, which replaces
  the decay statement: only boundedness is needed to beat a divergent archimedean part.
- **`exists_pos_ccmCorrectedSymbol`** — the choice of `R` with `W_a(R) > 0`.
- **`exists_characteristic_pair`** — equation `(3)`: a `tau > 0` with `W_a(tau) = W_a(-tau) = 0`,
  by the intermediate value theorem on `[0, R]` and evenness.

The Lean statement is slightly stronger than the card: no positivity of `a` is needed, only
`a < a_0`.

All statements are unconditional: `#print axioms` returns only
`[propext, Classical.choice, Quot.sound]`.
