# Squared-Xi parabolic heat-trace disproof lane

- **ID:** `squared-xi-parabolic-heat-trace-disproof`
- **Stage:** 1-in-progress
- **Type:** THEOREM TARGET / RH-FALSE completed Gaussian source
- **Scientific status:** `[BRIDGE PROVED ON PAPER] [HEAT ENDPOINT LEAN-FORMALIZED] [PARABOLIC LIMIT LEAN OPEN] [NO NEGATIVE VALUE YET]`
- **Parent:** `squared-xi-chebyshev-window-hankel-disproof.md`
- **Statement:** A parabolic joint limit of the translated reciprocal-Xi moments is the
  multiplicity-exact Gaussian heat trace of the entire centered Xi divisor.  Any strictly negative
  heat value is an unconditional proof that RH is false and forces a finite negative shifted
  reciprocal-moment witness.  The heat value has an exact completed prime/Gamma explicit formula.

## 1. Parabolic limit of the shifted reciprocal moments

For a multiplicity copy `q`, write

```text
z_q=(rho_q-1/2)*(-i),
lambda_q=z_q^(-2),
tau_y(lambda)=lambda/(1+y*lambda)=1/(y+z_q^2).           (1)
```

The corpus proves `Re(z_q^2)>0` unconditionally.  Let `y_j>0`, `y_j->infinity`, and let
`n_j` be natural numbers such that

```text
(n_j+1)/y_j -> t,          t>0.                          (2)
```

Then atomwise

```text
y_j^(n_j+1)*tau_(y_j)(lambda_q)^(n_j+1)
 =(1+z_q^2/y_j)^(-(n_j+1))
 ->exp(-t*z_q^2).                                       (3)
```

The convergence may be summed over the entire multiplicity-exact divisor.  To see this without a
zero-counting asymptotic, choose `Y` so large that `(n_j+1)/y_j>=t/2` and `tY/2>1`.  Put
`A_q=Re(z_q^2)>0`.  Since

```text
|1+z_q^2/y| >= 1+A_q/y,
y |-> y*log(1+A_q/y) is increasing,                     (4)
```

the tail of `(3)` is bounded by

```text
(1+A_q/Y)^(-tY/2).                                      (5)
```

The open zero strip and the unconditional squared-height bound give

```text
A_q=gamma_q^2-a_q^2 >= (7/9)*(gamma_q^2+a_q^2)
    =(7/9)*|z_q|^2.                                     (6)
```

After enlarging `Y` if necessary, `(5)` is bounded by a constant multiple of
`|z_q|^(-2)=|lambda_q|`.  The latter is summable in the formal corpus.  Dominated convergence
therefore proves

```text
lim_j y_j^(n_j+1)*T_(n_j)(y_j)
 =Theta_Xi(t),

Theta_Xi(t):=sum_q exp(-t*z_q^2).                       (7)
```

This is not the positive reciprocal-node thermal limit already in the corpus.  It is the entire
complex Xi divisor evolved by the Gaussian heat multiplier.

The unconditional sector bound, absolute summability, Schwarz reality, and negative-value
endpoint are formalized in `RHTower/XiGaussianHeatTraceDisproof.lean`.  The joint parabolic limit
and its all-divisor dominated-convergence interchange remain paper-only.

## 2. Unconditional RH-false endpoint

Schwarz and functional-equation symmetries make `Theta_Xi(t)` real.  If RH holds, every `z_q` is
real and hence every summand in `(7)` is strictly positive:

```text
RH -> 0<Theta_Xi(t).                                    (8)
```

Consequently

```text
Theta_Xi(t)<0 -> not RH.                                (9)
```

More strongly, `(7)` turns a negative heat value into a finite shifted-moment witness.  If
`Theta_Xi(t)<0`, then for all sufficiently large `j`,

```text
T_(n_j)(y_j)<0.                                         (10)
```

No parity adjustment or Hankel embedding is needed: RH makes every individual `T_n(y)`
nonnegative, so any value in `(10)` directly contradicts RH.  The formal endpoint is
`not_riemannHypothesis_of_xiShiftedReciprocalMoment_re_neg`.

## 3. Exact completed Gaussian source formula

The Riemann--Weil explicit formula applies unconditionally to the entire test

```text
h_t(z)=exp(-t*z^2),             t>0.                    (11)
```

whose multiplicative Fourier inverse is

```text
F_t(exp(u))=exp(-u^2/(4t))/(2*sqrt(pi*t)).               (12)
```

In Connes's normalization the result is

```text
Theta_Xi(t)
 =2*exp(t/4)-W_infinity(F_t)-Psi_prime(t),               (13)

Psi_prime(t)
 =sum_(n>=2) Lambda(n)/sqrt(n)
    *exp(-(log n)^2/(4t))/sqrt(pi*t),                    (14)

W_infinity(F_t)
 =(log(4*pi)+EulerGamma)*F_t(1)
  +integral_(0,infinity)
     (F_t(exp(u))+F_t(exp(-u))-2*exp(-u/2)*F_t(1))
     *exp(u/2)/(exp(u)-exp(-u)) du.                      (15)
```

Equations `(13)`--`(15)` retain the polar, Gamma, and every prime-power term in one convergent
completed value.  They are equations (14), (25), and (15) of Alain Connes,
*Heat Expansion and Zeta*, `https://arxiv.org/abs/2402.13082`.  That paper assumes RH only when it
interprets the ordinates as the spectrum of a self-adjoint operator.  The Riemann--Weil formula
it starts from sums the complex zeros and gives `(13)` for `Theta_Xi(t)` without RH.

## 4. Anti-theatre audit

- Small time is protected: the completed heat expansion begins with a positive
  `log(1/t)/(4*sqrt(pi*t))` divergence, while `(14)` is flat beyond every power.
- A prime-only estimate is invalid.  For moderate and large time, the pole, Gamma integral, and
  prime Gaussian sum undergo the same large cancellation encoded by `(13)`.
- Positivity of `Theta_Xi(t)` for a range of `t` is evidence only; a strict negative value is the
  required producer.
- The parabolic limit `(7)` is useful because it transports any source-side negative heat theorem
  back to an actual finite radial jet.  It does not assign that sign.

### Bare heat is not a complete off-line detector

The failure is structural, not merely an absent estimate.  Consider a finite symmetric spectral
packet consisting of four real copies at squared coordinate `r^2` and one off-real quartet whose
squared coordinates are `A+-iB`, with `A>=r^2`.  Its real Gaussian trace is

```text
4*exp(-t*r^2)+4*exp(-t*A)*cos(t*B).                     (16)
```

For every `t>=0`, `cos(tB)>=-1` and `exp(-tA)<=exp(-t*r^2)`, so `(16)` is nonnegative.  Thus an
off-real quartet can be masked at every heat time by lower real spectral mass.  This is exactly
the geometry expected if a hypothetical high Xi zero leaves the line while the known lower
critical-line divisor remains present.

Consequently the conjectured negative value below is a sufficient RH-disproof witness but not a
necessary consequence of false RH.  No asymptotic argument based only on the bare heat trace can
be treated as a complete route.  The live successor must use a real-axis-nonnegative polynomial
square times the Gaussian, so that a finite polynomial can cancel the lower packet before the
Gaussian suppresses the tail.

## Open source core

`[CONJECTURE -- WEAK PRODUCER]` There exists an exact `t>0` such that the completed source value
`(13)` is strictly negative.

The live task is a cancellation-preserving one-sided estimate for `(13)`, not separate bounds on
`W_infinity` and `Psi_prime` that destroy their completion.  A successful estimate gives the
finite witness `(10)` and then the formal RH-false endpoint.

Because of the masking theorem, failure to find such a time does not support RH and cannot retire
the filtered successor.

## Gates

- [x] atomwise parabolic limit
- [x] unconditional summable domination on paper
- [x] RH-positive and RH-false heat endpoints on paper
- [x] exact completed Gaussian prime/Gamma source formula identified
- [x] formalize `Theta_Xi`, its summability, and Schwarz reality
- [ ] formalize the all-divisor parabolic limit `(7)`
- [x] formalize `Theta_Xi(t)<0 -> not RiemannHypothesis`
- [x] formalize a negative individual shifted moment `-> not RiemannHypothesis`
- [x] prove the finite-packet masking no-go for the bare heat trace
- [ ] prove one strict negative completed source value in `(13)`
- [ ] transport that value to a finite shifted reciprocal-moment witness
