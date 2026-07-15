# Absolute-Euler paired energy reduces to one cumulative critical-error current

- **ID:** `absolute-euler-paired-cumulative-critical-error-current-law`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[VALUE RELATION]`, `[TOP-DOWN INTERFACE DISCHARGE]`
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT AN RH PROOF]`
- **Parents:**
  `absolute-euler-paired-translation-resolvent-functional-calculus.md`,
  `formal/GaloisForLFunctions/RHTower/CCMPolarPrimeStieltjesAutocorrelation.lean`
- **Statement:** On every absolute-Euler damped-sine packet, all individual critical prime-power
  autocorrelations and both polar resolvents combine into one integral of the derivative of the
  packet autocorrelation against the cumulative completed critical-Mellin error.  The remaining
  RH inequality is a comparison between this single arithmetic current and the compensated
  digamma resolvent form.

## 1. Packet autocorrelation

Let

```text
y(x)=sum_j r_j exp(-a_j*x) sin(b_j*x),  a_j>1/2,         (1)
C_y(h)=integral_0^infinity y(x+h)y(x) dx,  h>=0.         (2)
```

The sum is finite and the coefficients are real.  Therefore `C_y` is continuously
differentiable,

```text
C_y'(h)=integral_0^infinity y'(x+h)y(x) dx,              (3)
```

and both `C_y(h)` and `C_y'(h)` decay like `exp(-a*h)` for some `a>1/2`.

Write the cumulative critical polar--prime error as

```text
E_crit(h)
 =4*sinh(h/2)
  -sum_(2<=m<=exp(h)) Lambda(m)*m^(-1/2).                (4)
```

This is `criticalMellinCompletedError h` in the formal corpus.

## 2. Infinite-aperture Stieltjes boundary law

The formal finite-aperture theorem
`criticalMellinStieltjesPairing_integrationByParts` proves, for a smooth autocorrelation `C`
whose aperture endpoint vanishes,

```text
integral_0^H 2*cosh(h/2)*C(h) dh
 -sum_(2<=m<=exp(H)) Lambda(m)*m^(-1/2)*C(log m)
 =-integral_0^H E_crit(h)*C'(h) dh.                      (5)
```

Choose a smooth cutoff `chi_A` which is one on `[0,A]` and zero beyond `A+1`.  Apply `(5)` to the
zero extension of `y*chi_A`, with any symmetric aperture containing its support, and then let `A`
tend to infinity.  On every fixed compact lag interval the compactly supported autocorrelations
and their derivatives converge to `(2)--(3)`.  The exponential packet bound and the elementary
Chebyshev bound

```text
sum_(m<=x) Lambda(m)=O(x log x)                           (6)
```

give an integrable majorant because `a>1/2`.  They also make the terminal product
`E_crit(H)C_y(H)` tend to zero.  Dominated convergence therefore gives

```text
integral_0^infinity 2*cosh(h/2)*C_y(h) dh
 -sum_(m>=2) Lambda(m)*m^(-1/2)*C_y(log m)
 =-integral_0^infinity E_crit(h)*C_y'(h) dh.             (7)
```

No prime number theorem remainder estimate is needed for this passage; the strict packet damping
`a>1/2` beats the elementary critical exponential growth.

## 3. Exact completed paired identity

Let

```text
D_Gauss
 =-(log(pi)+EulerGamma)/2 * I
   +sum_(n>=0) (1/(2*(n+1))*I-R_(2*n+1/2)),              (8)
```

with the compensated series interpreted on the finite damped-sine core.  The two omitted
resolvents `R_(1/2)+R_(-1/2)` have kernel

```text
exp(-h/2)+exp(h/2)=2*cosh(h/2).                          (9)
```

Hence the translation-resolvent identity of the parent card and `(7)` give

```text
sum_(j,k) r_j*r_k P[L](w_j,w_k)
 =8*(
     <y,D_Gauss y>
     -integral_0^infinity E_crit(h)*C_y'(h) dh
   ).                                                     (10)
```

Equation `(10)` is the complete absolute-Euler paired Xi value.  Every individual prime and
prime power has disappeared into the one canonical cumulative source `E_crit`.

## 4. Top-down consequence

The absolute-Euler paired completeness theorem now gives the chain

```text
integral_0^infinity E_crit(h)*C_y'(h) dh
  <= <y,D_Gauss y>
for every rational damped-sine packet y
  -> absolute-Euler paired source passivity
  -> positivity on the Xi--Hurwitz orientation vector
  -> RH.                                                   (11)
```

Thus the infinite prime-source obligation has been reduced to one source-current comparison.
This is not a sign claim for `E_crit` alone: `C_y'` changes sign for general damped-sine packets,
and positive density or a pointwise Chebyshev bound cannot replace the coupled inequality `(11)`.

The exact remaining theorem is:

> **[OPEN]** Prove the compensated digamma resolvent form dominates the cumulative critical-error
> current on the rational damped-sine core, using a source-specific cancellation or reflection
> identity rather than Xi divisor orientation.

It is separate from the active anisotropic theta-current/subpower route.  It uses the same prime
source but a fixed half-line autocorrelation geometry and no Taylor meshes.

## 5. What the formal corpus already provides

`CCMPolarPrimeStieltjesAutocorrelation.lean` already formalizes all finite-aperture algebra needed
before the limit:

- `criticalMellinStieltjesPairing_cexp_re`;
- `polarPrimeAutocorrelationQuadratic_eq_integral_sub_sum`;
- `criticalMellinStieltjesPairing_integrationByParts`;
- `polarPrimeAutocorrelationQuadratic_integrationByParts_of_support`;
- `criticalMellinStieltjesCumulative_eq_criticalErrorForm`.

The paper-only additions are the damped-sine infinite-aperture passage and its composition with
the Gauss-resolvent identity.  Under the active no-computation/no-build boundary they are not
promoted to stage 3.

## Gates

- [x] packet autocorrelation differentiability and exponential decay
- [x] finite-aperture formal Stieltjes identity located
- [x] infinite-aperture boundary term and dominating majorant discharged on paper
- [x] all prime lags compressed to the cumulative critical error
- [x] exact completed paired identity `(10)` derived
- [x] non-circular source-current target isolated
- [ ] prove the digamma/current domination `(11)`
- [ ] formalize the infinite-aperture passage after the analytic inequality is found
- [ ] prove RH
