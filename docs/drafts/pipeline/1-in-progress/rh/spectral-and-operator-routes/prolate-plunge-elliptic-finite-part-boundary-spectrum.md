# Prolate plunge has an elliptic finite-part arithmetic boundary spectrum

- **ID:** `prolate-plunge-elliptic-finite-part-boundary-spectrum`
- **Stage:** 1-in-progress
- **Type:** EXACT MODEL THEOREM + FAILED RH-BRIDGE CANDIDATE
- **Scientific status:** `[MODEL THEOREM PROVED HERE] [PSWF TRANSFER NOT YET PROVED]`
  `[PROPOSED RH BRIDGE FALSIFIED BY CATEGORY MISMATCH]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE — NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `constrained-prolate-radial-leakage-divisibility-spectrum.md`,
  `constrained-prolate-arithmetic-dilation-operator-limit.md`,
  `cofinal-prolate-weil-relative-normal-form-conjecture.md`, and
  `ccm-universal-boundary-laplace-frame-saturation-law.md`
- **Statement:** The fixed-turning-parameter exterior leakage models interpolate exactly through
  incomplete elliptic integrals. As the turning parameter approaches the plunge, normalized mass
  collapses to the band edge, but the von-Mangoldt logarithmic divisor mask annihilates that
  leading coordinate. After the unique elliptic finite-part rescaling, the surviving positive
  arithmetic spectrum is

  ```text
  kappa_boundary(k)
   =2*log(k)/k*atanh(1/k),                 k>=2.
  ```

  The exact model theorem is proved below. A fixed-`sigma` transfer in weighted projective norm to
  actual proportional-degree PSWFs may still be possible, after repairing admissibility and
  normalization. It cannot supply the proposed RH bridge: the limit is stationary same-edge
  radial data, whereas fixed-width rectangular Weil completeness is carried by a moving
  cross-edge tent at lag near twice the aperture.

## Why this is the first plausible prolate--boundary bridge

The fixed-mode radial theorem gives the arcsine spectrum

```text
log(k)/k*arcsin(1/k).
```

That theorem lives at turning parameter `sigma=0`. The complete two-edge detector instead lives
in the noncompact boundary channel, while the cofinal prolate normal-form card leaves their
coupling open. Simply letting the prolate depth grow does not identify this channel.

The radial Bessel square at a fixed turning parameter `0<=sigma<1` has geometric mean density

```text
dm_sigma(x)
 =dx/sqrt((x^2-1)*(x^2-sigma^2)),          x>1.            (EP1)
```

At `sigma=0`, `(EP1)` is the proved fixed-mode density up to normalization. At `sigma->1`, it
develops a logarithmic band-edge mass. The result below identifies both the singular coordinate
and its first finite part exactly. The arithmetic mask `log(k)` kills the singular coordinate
because `log(1)=0`; this is a source operation, not an imposed subtraction.

## Exact elliptic model theorem

For `0<=sigma<1`, define

```text
K_sigma
 =integral_1^infinity
    dx/sqrt((x^2-1)*(x^2-sigma^2)),

T_sigma(k)
 =integral_k^infinity
    dx/sqrt((x^2-1)*(x^2-sigma^2)),        k>=1,

w_sigma(k)=T_sigma(k)/(k*K_sigma).                           (EP2)
```

### Theorem EP-A: exact elliptic interpolation

The substitution `u=1/x` gives

```text
K_sigma
 =integral_0^1 du/sqrt((1-u^2)*(1-sigma^2*u^2)),

T_sigma(k)
 =integral_0^(1/k) du/sqrt((1-u^2)*(1-sigma^2*u^2)).       (EP3)
```

Thus `K_sigma` is the complete Legendre elliptic integral and `T_sigma(k)` is its incomplete
version at amplitude `arcsin(1/k)`. In particular,

```text
K_0=pi/2,
T_0(k)=arcsin(1/k),
w_0(k)=2/(pi*k)*arcsin(1/k).                               (EP4)
```

This is exactly the shape of the fixed-mode prolate dilation spectrum.

**Proof.** Under `x=1/u`,

```text
dx=-du/u^2,
sqrt((x^2-1)*(x^2-sigma^2))
 =sqrt((1-u^2)*(1-sigma^2*u^2))/u^2.
```

The factors `u^-2` cancel. The endpoints `x=1,infinity` become `u=1,0`, and
`x=k,infinity` become `u=1/k,0`. Setting `sigma=0` gives the elementary arcsine integrals.
`QED`

### Theorem EP-B: endpoint collapse and finite part

As `sigma` increases to one,

```text
K_sigma ->infinity,
K_sigma
 =log(4/sqrt(1-sigma^2))
   +O((1-sigma^2)*log(1/(1-sigma^2))),
w_sigma(1)=1,
w_sigma(k)->0                              for every k>=2,   (EP5)
```

but for every fixed `k>=2`,

```text
K_sigma*w_sigma(k)
 =T_sigma(k)/k
 ->atanh(1/k)/k.                                            (EP6)
```

Equivalently, if `P_1` is the diagonal rank-one coordinate at `k=1`, then

```text
K_sigma*(diag(w_sigma)-P_1)
 ->diag(0, atanh(1/2)/2, atanh(1/3)/3, ...).                (EP7)
```

The convergence in `(EP7)` holds in every diagonal weighted trace norm with weight bounded by
`C*(1+log k)`.

**Proof.** The integrand in `(EP3)` increases pointwise with `sigma`. Its limit for `u<1` is
`1/(1-u^2)`. Hence, for `k>=2`, monotone convergence gives

```text
T_sigma(k)
 ->integral_0^(1/k)du/(1-u^2)
 =atanh(1/k).                                               (EP8)
```

For `K_sigma`, the same limiting integral diverges at `u=1`. The displayed logarithmic scale is
the classical `k->1` expansion of the complete Legendre integral, with complementary modulus
`sqrt(1-sigma^2)`. Also `T_sigma(1)=K_sigma`, proving `w_sigma(1)=1`;
`(EP5)`--`(EP7)` follow.

For weighted trace convergence, monotonicity gives

```text
0<=T_sigma(k)<=atanh(1/k),                 k>=2.            (EP9)
```

Since `atanh(1/k)<=C/k` for `k>=2`,

```text
sum_(k>=2)(1+log k)*atanh(1/k)/k<infinity.                  (EP10)
```

Dominated convergence applied to `(EP8)` proves the claimed weighted `ell^1`, hence diagonal
weighted trace-norm, convergence. `QED`

### Theorem EP-C: the arithmetic mask principalizes the plunge

Define the symmetrized divisor-mask eigenvalues

```text
kappa_sigma(k)=2*log(k)*w_sigma(k).                         (EP11)
```

Then the singular coordinate is identically absent,

```text
kappa_sigma(1)=0,                                           (EP12)
```

and

```text
K_sigma*kappa_sigma(k)
 ->kappa_boundary(k)
 :=2*log(k)/k*atanh(1/k),                  k>=2,            (EP13)
```

with `ell^1` convergence of the complete eigenvalue sequence. Therefore the boundary operator

```text
A_boundary=diag(kappa_boundary(k))_(k>=2)                   (EP14)
```

is positive and trace class.

This is the precise positive survivor: the prolate plunge has a divergent leading leakage
coordinate, but the arithmetic anticommutator does not see it. Its first nonzero source scale is
the positive trace-class atanh spectrum `(EP14)`.

### Exact zeta-derivative transform

The positive Taylor series

```text
atanh z=sum_(j>=0) z^(2j+1)/(2j+1),          |z|<1
```

and Tonelli give

```text
sum_(k>=2)log(k)/k*atanh(1/k)
 =-sum_(j>=0) zeta'(2j+2)/(2j+1).                          (EP15)
```

Thus `(EP14)` is the plunge-boundary analogue of the fixed-mode arcsine/zeta-derivative spectrum:
the central-binomial arcsine coefficients are replaced by the odd harmonic coefficients
`1/(2j+1)`.

## Logarithmic boundary coordinate

Writing `x=exp(r)` turns `(EP1)` into

```text
dm_sigma(r)
 =exp(r)dr/
   sqrt((exp(2r)-1)*(exp(2r)-sigma^2)).                     (EP16)
```

At the plunge,

```text
dm_1(r)=dr/(2*sinh r)
        =exp(-r)/(1-exp(-2r))dr.                            (EP17)
```

The tail identity is

```text
integral_(log k)^infinity dr/(2*sinh r)=atanh(1/k).         (EP18)
```

Equation `(EP17)` is a genuine boundary density of Gamma type: it has the same hyperbolic
denominator that appears in completed archimedean lag formulas. This resemblance does **not**
identify it with `suzukiRectangularCompletedArchLagKernel`. More strongly, the aperture-independent
stationary density cannot encode the translated cross-edge tent that makes the rectangular
family complete. The resemblance therefore does not define an RH source/profile bridge.

## Conjectural transfer to actual PSWFs

For each fixed `sigma<1`, Dunster's proportional-degree radial expansion and Bessel averaging
predict a normalized **positive-half** exterior leakage law

```text
actual positive-half exterior probability
 ->dm_sigma/K_sigma.                                       (EP19)
```

Here the normalization must be the positive-half leakage `d^+`. If `d` denotes total two-sided
exterior leakage, then `d=2d^+` for the parity eigenfunctions and the law normalized by `d` has
total mass `1/2`. In particular, the unqualified formula below was off by a factor of two:

```text
K_(sigma_j)*A_(gamma_j,n_j)/d^+_(gamma_j,n_j)
 ->A_boundary,

K_(sigma_j)*A_(gamma_j,n_j)/d_(gamma_j,n_j)
 ->(1/2)*A_boundary.                                        (EP20)
```

These formulas remain conjectural even for a diagonal sequence.

There is also an admissibility defect in using a single proportional-degree even PSWF: its
integral need not vanish. A source-side transfer must instead use an exact zero-integral
combination such as

```text
g_(n,gamma)
 =(e_(n,gamma)-(ell_n/ell_0)e_(0,gamma))
   /sqrt(1+(ell_n/ell_0)^2).                                (EP20a)
```

The corpus fixed-mode secular estimates suggest that the `e_0` correction has exponentially
smaller exterior leakage when the turning action is strictly below the fixed-mode action, but
that estimate has not been proved in the proportional-degree regime required here.

## Hostile audit

1. **No uniform plunge theorem has been proved.** Dunster's stated constants are uniform only for
   `sigma<=sigma_0<1`. An iterated limit and diagonal selection avoid claiming uniformity, but
   weighted projective convergence still requires quantitative tail control.
2. **Off-diagonal terms may return after multiplication by `K_sigma`.** Fixed-`sigma`
   off-diagonal decay is not enough. One must prove

   ```text
   K_(sigma_j)*sum_(p!=q)(1+log p+log q)
     |G_(gamma_j,n_j)(p,q)|/d^+_(gamma_j,n_j)->0.           (EP21)
   ```

   A diagonal choice over finitely many coordinates does not by itself control the infinite
   weighted tail.
3. **The original source was inadmissible.** A single even proportional-degree PSWF generally has
   nonzero integral. The exact repair `(EP20a)` is harmless only after proving its coefficient and
   exterior cross terms are negligible on the selected scale.
4. **The arithmetic mask, not the zero-integral constraint, kills the leading coordinate.**
   The singular coordinate is dilation index `k=1`, whereas zero integral is Fourier evaluation
   at frequency zero. Conflating them would be a category error. Equation `(EP12)` is the exact
   cancellation.
5. **A positive prime spectrum is not Weil positivity.** The raw prime term enters the Weil form
   with a negative sign. The missing theorem must identify the archimedean/polar finite part at
   the same `d/K_sigma` scale and prove the completed comparison.
6. **Fatal category mismatch with rectangular completeness.** The fixed-width rectangular
   detector has a moving cross-edge tent supported near lag `2a`; as aperture `a` grows, its
   arithmetic signal moves to indices of size about `exp(2a)`. The limit `(EP14)` is
   aperture-independent same-edge diagonal data. Proving `(EP21)` would erase, rather than retain,
   the only coherent off-diagonal/cross-edge channel available to carry that moving signal.
   Therefore `(EP20)` cannot be the missing rectangular source/profile bridge.
7. **No RH claim.** Even a corrected fixed-`sigma` transfer plus the exact trace `(EP15)` would
   only construct a stationary arithmetic boundary carrier. It would not establish the sign
   required by the complete two-edge detector.
   boundary carrier. It would not establish the sign required by the complete two-edge detector.

## Research process and novelty

### Internal search

Statement-level searches across `formal/` and the full pipeline found the fixed-mode
`arcsin(1/k)` spectrum, boundary-profile saturation, and the open prolate/two-edge decomposition,
but no `atanh(1/k)`, elliptic finite-part plunge spectrum, or arithmetic principalization
statement.

### Primary literature

- Dunster gives the uniform fixed-compact-`sigma` radial Bessel approximation and the
  proportional-degree quantization law.
- Bonami--Karoui use the complete Legendre elliptic integral in uniform PSWF estimates and
  endpoint normalization.
- DLMF records the classical spheroidal and elliptic-function infrastructure.

The elliptic substitutions `(EP3)`, endpoint limit `(EP8)`, and trace-class dominated-convergence
argument are classical analysis. Candidate novelty is restricted to their joint use as:

```text
fixed prolate arcsine spectrum
 -> elliptic turning-parameter family
 -> arithmetic annihilation of the plunge coordinate
 -> positive atanh finite-part boundary spectrum.          (EP22)
```

Search absence is not priority. Status remains `[NOVELTY UNVERIFIED]`.

## Verdict and positive survivor

The proposed RH bridge is retired. Its failure is not lack of an estimate: it asks a stationary
same-edge diagonal limit to reproduce a moving cross-edge detector. No strengthening of `(EP21)`
repairs that loss of aperture translation.

The positive survivor is the exact elliptic finite-part theorem `(EP3)`--`(EP15)`, together with
the corrected one-sided normalization in `(EP20)`. A fixed-`sigma` PSWF transfer would be an
independent operator theorem, not an RH bridge. Do not formalize a conditional wrapper. Formalize
the model theorem only after independent audit and novelty review; any actual PSWF transfer must
first prove admissibility of `(EP20a)`.

## Gates

- [x] internal statement-level corpus search
- [x] preliminary primary-literature search
- [x] exact elliptic interpolation
- [x] exact band-edge collapse
- [x] weighted trace-class finite-part limit
- [x] arithmetic annihilation of the singular coordinate
- [x] exact atanh/zeta-derivative trace
- [ ] independent hostile audit of `(EP3)`--`(EP15)`
- [ ] fixed-`sigma` actual PSWF leakage transfer
- [ ] admissible-source repair `(EP20a)`
- [x] positive-half versus total-leakage normalization corrected
- [x] moving cross-edge category mismatch identified
- [x] RH bridge retired
- [ ] exact model theorem novelty audit
- [ ] exact model theorem Lean formalization, if novelty survives
