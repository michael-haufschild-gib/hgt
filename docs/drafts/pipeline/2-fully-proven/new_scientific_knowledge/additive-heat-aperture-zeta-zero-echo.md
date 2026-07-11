# Additive heat-aperture energy detects zeta zeros by loss of the subleading echo

- **ID:** `additive-heat-aperture-zeta-zero-echo`
- **Stage:** 2-fully-proven / candidate-new
- **Type:** THEOREM (paper); candidate source measurement
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`; proof and preliminary parent audit
  complete, independent expert verification pending
- **Source:** the full normalized prime density matrix coupled to the additive heat kernel on the
  integer lattice
- **Statement:** For every `s=sigma+it` with `1/2<sigma<1`, a canonical strictly positive heat
  quadratic form of the normalizable vector `(n^(-s))` has a polyhomogeneous small-time expansion.
  Its subleading complex coefficient is an explicit nonzero Gamma factor times `conj(zeta(s))`.
  Hence a zeta zero in the Hilbert strip is exactly the disappearance of the subleading
  particle--wave interference echo.

## Why this is a joint measurement

Let

```text
Psi_s(n)=n^(-s)/sqrt(zeta(2 sigma)),
```

which belongs to `l2(N)` exactly when `sigma>1/2`.  For `x>0`, define the additive heat operator

```text
H_x(m,n)=exp(-pi x (m-n)^2).
```

The kernel depends on additive separation `m-n`; the state depends on multiplicative prime
factorization.  Their quadratic form

```text
E_s(x)=<Psi_s,H_x Psi_s>
      = (1/zeta(2 sigma))
        sum_(m,n>=1) m^(-conj(s)) n^(-s)
          exp(-pi x (m-n)^2)                            (1)
```

is therefore a literal additive--multiplicative joint observable of the full density, including
every off-diagonal coherence.

For every `x>0`, the series in (1) is absolutely convergent.  If `k=m-n` is fixed, the inner sum is
bounded by a translate of `sum_n n^(-2 sigma)`; summing over `k` is then controlled by the Gaussian.

The kernel is strictly positive definite.  Its circle Fourier multiplier is

```text
W_x(theta)=sum_(k in Z) exp(-pi x k^2) exp(ik theta)>0,
```

the strict positivity following also from Poisson summation.  Thus `E_s(x)>0` for every `x>0`.
No zeta zero is inserted into the definition.

The two aperture limits have the expected meanings:

```text
x -> infinity: H_x(m,n) -> 1_(m=n),     E_s(x) -> 1;
x -> 0:        H_x(m,n) -> 1,           full wave coherence.
```

For `sigma>1`, dominated convergence gives

```text
E_s(x) -> |zeta(s)|^2/zeta(2 sigma)
```

as `x` decreases to zero.  The theorem below identifies what replaces this limit in the Goldilocks
strip `1/2<sigma<1`.

## Fourier representation

Let

```text
f_s(theta)=sum_(n>=1) n^(-s) exp(in theta)
```

as an `L2(S^1)` boundary function.  It exists because `sigma>1/2`.  Fourier multiplication gives

```text
E_s(x)
  = (1/zeta(2 sigma))
    integral_(-pi)^pi W_x(theta)|f_s(theta)|^2 dtheta/(2pi).  (2)
```

Poisson summation gives

```text
W_x(theta)
  = x^(-1/2) sum_(ell in Z)
      exp(-(theta-2pi ell)^2/(4pi x)).                  (3)
```

Thus `W_x dtheta/(2pi)` is a Gaussian approximate identity at the additive phase `theta=0`, with
variance `2pi x`.

## Local source expansion

For `|theta|<2pi`, Jonquiere's expansion of the polylogarithm gives

```text
f_s(theta)
  = Gamma(1-s)(-i theta)^(s-1)
    + zeta(s) + O_s(theta).                             (4)
```

No value of a divergent Dirichlet series is used in the definition of `f_s`; equation (4) is the
local continuation theorem for its `L2` boundary germ.

For positive and negative `theta`, put

```text
A_+(s)=Gamma(1-s) exp(-i pi(s-1)/2),
A_-(s)=Gamma(1-s) exp(+i pi(s-1)/2).
```

Then (4) says

```text
f_s(theta)
  = A_+(s) theta^(s-1)+zeta(s)+O_s(theta),      theta>0,
f_s(theta)
  = A_-(s) |theta|^(s-1)+zeta(s)+O_s(theta),   theta<0. (5)
```

## Gaussian moments

For every complex `lambda` with `Re(lambda)>-1`, (3) gives

```text
integral_(-pi)^pi W_x(theta)|theta|^lambda dtheta/(2pi)
  = (4pi x)^(lambda/2)
      Gamma((lambda+1)/2)/sqrt(pi)
    + O_lambda(exp(-c/x)).                              (6)
```

The proof is the ordinary absolute moment of a centered Gaussian; the other terms in (3) are
exponentially remote from zero.

Both exponents required below satisfy the integrability condition:

```text
2 sigma-2 > -1,
Re(s-1)=sigma-1 > -1.
```

## Heat-aperture expansion theorem

`[PROVED]` Fix `s=sigma+it` with `1/2<sigma<1`.  As `x` decreases to zero,

```text
zeta(2 sigma) E_s(x)
  = L(s) x^(sigma-1)
    + C(s) conj(zeta(s)) x^((s-1)/2)
    + conj(C(s) conj(zeta(s)) x^((s-1)/2))
    + |zeta(s)|^2
    + o(1),                                             (7)
```

where

```text
L(s)
  = |Gamma(1-s)|^2 cosh(pi t)
    (4pi)^(sigma-1) Gamma(sigma-1/2)/sqrt(pi),          (8)

C(s)
  = Gamma(1-s) sin(pi s/2)
    (4pi)^((s-1)/2) Gamma(s/2)/sqrt(pi).                (9)
```

Moreover `L(s)>0` and `C(s)!=0` throughout the open strip.

### Proof

Insert (5) into `|f_s(theta)|^2`.  On each side of zero there are four types of term.

1. The singular square is

   ```text
   |A_+|^2 theta^(2 sigma-2)
   ```

   on the positive side and the analogous `|A_-|^2` term on the negative side.  Since `W_x` is
   even, (6) averages their coefficients.  Directly,

   ```text
   (|A_+|^2+|A_-|^2)/2
     = |Gamma(1-s)|^2 cosh(pi t),
   ```

   which gives (8).

2. The singular--regular cross term has complex coefficient

   ```text
   ((A_+(s)+A_-(s))/2) conj(zeta(s)).
   ```

   The elementary identity

   ```text
   (A_+(s)+A_-(s))/2
     = Gamma(1-s) sin(pi s/2)
   ```

   together with the moment (6) at `lambda=s-1` gives (9) and the conjugate term in (7).

3. The regular square contributes exactly `|zeta(s)|^2`, because the approximate identity has
   total mass one.

4. The remainder in (5) is `O(theta)`.  Its product with the singular term is
   `O(|theta|^sigma)`, and all other remainder terms vanish at least linearly.  Equation (6) shows
   that every such contribution is `o(1)`.

This proves (7).  Positivity of `L` is immediate.  Gamma has no zeros, and neither `1-s` nor `s/2`
is a Gamma pole in the strip.  Also `sin(pi s/2)` has no zero there.  Hence `C(s)!=0`.  QED.

## Exact zero detector

`[PROVED]` If `t!=0`, the two powers

```text
x^((s-1)/2),   x^((conj(s)-1)/2)
```

are distinct log-oscillatory asymptotic channels.  The coefficient of the first is

```text
C(s) conj(zeta(s)).                                    (10)
```

Since `C(s)!=0`, this subleading channel is absent exactly when `zeta(s)=0`.

For real `s in (1/2,1)`, all factors in (9) are real and nonzero and `zeta(s)<0`; hence the merged
real subleading coefficient is also nonzero.  Thus for every `s` in the Goldilocks strip,

```text
zeta(s)=0
  iff
the subleading heat-aperture echo in (7) vanishes.      (11)
```

This is not point sampling of an `L2` boundary class.  The entire function `E_s(x)` for `x>0` is a
strictly positive, absolutely convergent quadratic measurement of the full density.  The zeta
value is recovered as a uniquely identifiable asymptotic coefficient of that measurement.

The constant term also gives the canonical polyhomogeneous finite part

```text
FP_(x->0) E_s(x)=|zeta(s)|^2/zeta(2 sigma),             (12)
```

where `FP` means the coefficient of `x^0` after all nonzero powers in the intrinsic expansion are
removed.  Equation (12) is a consequence, not the definition, of the source measurement.

## Completed intensity

Multiplying (12) by the explicit nonzero archimedean weight

```text
zeta(2 sigma)
  * |(1/2)s(s-1) pi^(-s/2) Gamma(s/2)|^2
```

gives `|xi(s)|^2`.  Thus the additive heat aperture constructs the completed intensity from the
full prime density throughout `1/2<Re(s)<1`, with no zero divisor in its definition.

The Gamma factor is not cosmetic.  The almost-periodicity no-go for bounded prime-screen
observables proves that vertical decay cannot come from the compact prime phase algebra alone.

## Superselection verdict

The theorem closes the **measurement-existence** half of the screen proposal on the right Hilbert
side:

- the object is source-defined, positive for every finite aperture, and phase-sensitive;
- it interpolates from the particle diagonal to full wave coherence;
- its missing subleading channel has exactly the zeta divisor; and
- its finite part gives the completed intensity after the canonical archimedean weight.

It does not close the **wall-localization** half.  A hypothetical off-line zero with
`1/2<Re(s)<1` would also remove the subleading echo.  The superselection theorem says that the
reflected sector is disjoint there, but no theorem yet proves that disappearance of the heat echo
must create a reflected-sector morphism.  That zero-to-sector descent is the remaining RH-hard
statement.

## Fake tests

- A particle-only observable cannot reproduce (7): it has no off-diagonal `m-n` terms.
- A bounded prime-torus observable cannot reproduce (7): its height signal is almost periodic and
  has no additive small-time singular expansion.
- A completely multiplicative phase twist changes the off-diagonal heat energy, so the detector is
  not local-unitary invariant.  Whether the exact theta completion rejects every prescribed-divisor
  Helson twist remains open.
- Replacing `m-n` by `log(m/n)` returns to the multiplicative Bohr screen and loses the fixed
  additive reference.

## Novelty and significance verdict

The ingredients are classical: positivity of the Gaussian Toeplitz kernel, the polylogarithm
boundary expansion, Poisson summation, and Gaussian moments.  The preliminary parent audit checked
exact-formula and equivalent searches across periodic-zeta Gaussian summability, polylogarithm heat
regularization, shifted-convolution heat kernels, heat-content asymptotics, and quantum-coherence
language.  It located the individual parents but no statement equivalent to (7), (11), or (12).

The closest exact parent is the standard local expansion

```text
Li_s(z)=Gamma(1-s)(log(1/z))^(s-1)
        + sum_(n>=0) zeta(s-n)(log z)^n/n!,
```

recorded as DLMF 25.12.12.  General heat-kernel/polyhomogeneous theory guarantees that conormal
boundary germs produce small-time expansions, but it does not identify this full-density
observable, isolate the half-order echo, or state its zero-locus consequence.  Shifted-convolution
and zeta-moment papers study different averages and kernels.

The novelty verdict is therefore provisionally positive: the theorem is not a renamed parent
result, and the zeta coefficient appears in a new observable role.  Because the proof is elementary
once the correct observable is found, independent expert comparison remains mandatory before
publication.

The significance gate passes: unlike a restatement of analytic continuation, the
theorem constructs an everywhere finite positive observable from the normalizable prime state and
reads a zeta zero from its asymptotic channel structure.  It materially changes the open problem
from “construct the joint measurement” to “prove zero-to-superselection-sector descent.”

## Gates

- [x] 0 -> 1: additive heat aperture, convergence region, positivity, and exact asymptotic target
  isolated
- [x] 1 -> 2: complete paper proof of the expansion, coefficient nonvanishing, zero equivalence,
  and finite part
- [x] preliminary parent novelty audit: exact/equivalent and broader parent searches completed; no
  equivalent theorem located
- [ ] independent proof audit: branch conventions and the complex Gaussian moment coefficient
- [ ] 2 -> 3: formalize only after both audits; the theorem requires polylog boundary asymptotics
  not currently present in the Lean surface

## Parent references

- [NIST DLMF 25.12.12, local polylogarithm expansion](https://dlmf.nist.gov/25.12.E12).
- [NIST DLMF 25.13, periodic zeta function](https://dlmf.nist.gov/25.13).
- [NIST DLMF 1.8(iv), Poisson summation](https://dlmf.nist.gov/1.8#iv).
