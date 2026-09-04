# Prime-log congruence cubic ideal-exit law

- **ID:** ULF-PLCIE-001
- **Stage:** 2-fully-proven
- **Type:** unconditional pre-divisor source-flow/ideal-boundary law
- **Parents:** ULF-PCOB-001, ULF-PHIN-001, ULF-SACWHT-001
- **Status:** `[PAPER-PROVED] [LEAN-IN-PROGRESS] [NOT RH]`

## 1. Statement

For `d>0`, let

```text
w_d(p)=8d log(p) p^(-(1+2d))
```

be the literal transported Stokes prime density, and let `T_d` be the normalized prime--Hodge
integral--nuclear operator of ULF-PCOB-001.  The inverse prime-heat congruence at time `u>=0` is

```text
P_(-u)e_p=p^u e_p,              T_(d,u)=P_(-u) T_d P_(-u).
```

Its prime diagonal before the harmless positive normalization is

```text
w_(d,u)(p)=p^(2u)w_d(p)
            =8d log(p) p^(-(1+2(d-u))).                     (PLCIE.1)
```

Then

```text
sum_p w_(d,u)(p)<infinity  iff  u<d.                         (PLCIE.2)
```

Consequently `d` is intrinsic to the formed operator:

```text
d=sup{u>=0 : P_(-u)T_dP_(-u) is trace class}.                (PLCIE.3)
```

Every finite-prime compression crosses `u=d` by an invertible diagonal gauge.  The complete
source does not: its trace-ideal exit occurs exactly at `u=d`.  Thus the deformation is invisible
at every finite semilocal stage and nontrivial only after cofinal source completion.

The endpoint has an exact first-clock density

```text
log(p) w_(d,d)(p)=8d (log p)^2/p.                            (PLCIE.4)
```

This is the same coefficientwise ray as the universal formation metric anomaly in
`DirectSubunitEscapeCapacityFusion`; no prime-dependent fit is needed.  This statement is
projective only: the source coefficient is `8d`, whereas the Xi-copy coefficient is
`115/(864 a^4)`.  No source law identifying those scalars is proved here.

Finally the forward congruence orbit `P_uT_dP_u` has the cubic source jet

```text
d^3/du^3(P_uT_dP_u)|_(u=0)
 =-S_Lambda^3(T_d)
 =-8 Phi tensor |b_d><b_d|,                                 (PLCIE.5)
```

by ULF-PCOB-001.  Equations `(PLCIE.2)` and `(PLCIE.5)` are two aspects of one source orbit: its
infinitesimal top jet is the unique cubic birth, while its reflected maximal time is the
non-trace-class completion wall.

## 2. Proof

Equation `(PLCIE.1)` is the real-power law.  If `u<d`, put `delta=d-u>0`.  Then

```text
w_(d,u)=(d/delta)w_delta,
```

and `w_delta` is summable by
`summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight`.

If `u>=d`, then `p^(2(u-d))>=1` and `log p>=log 2`, so

```text
w_(d,u)(p)
 =8d (log p)/p * p^(2(u-d))
 >=8d log(2)/p.
```

The prime harmonic series diverges, proving the reverse implication.  Positivity of `T_d` makes
trace-class membership equivalent to summability of its diagonal; its history marginal has trace
one and its prime normalization is a fixed positive scalar.  This proves `(PLCIE.2)--(PLCIE.3)`.
Finite compressions are finite dimensional.  Equation `(PLCIE.4)` is immediate at `u=d`.

For `(PLCIE.5)`, differentiate `P_uT_dP_u` three times on PCOB's Schatten domain.  The binomial
Leibniz expansion is

```text
-(Lambda^3T_d+3Lambda^2T_dLambda
  +3Lambda T_dLambda^2+T_dLambda^3)=-S_Lambda^3(T_d),
```

and PCOB identifies the last expression with the displayed rank-one source birth.  PCOB also
proves every mixed term extends Hilbert--Schmidt, justifying the Schatten derivative.

## 3. What this proves—and does not

- It is not positivity selection: positivity is used only to read trace-ideal membership from the
  diagonal.
- It is not regularization: `u=d` is forced as the maximal ideal time of the actual source flow.
- It is not a quadratic cross-prime form: the orbit's distinguished infinitesimal datum is its
  cubic PCOB jet.
- It is not a phase choice: `P_u` changes singular values and has unbounded reflected inverse.
- It does not identify the scalar normalization of the exit ray with the Xi metric anomaly.
- It does not prove that the ideal-exit boundary class equals Xi escape multiplicity.  That remains
  the exact arithmetic realization gate in ULF-PHCCED-001.

## 4. New completion target

The completion extension should be built over the half-open source-history interval `0<=u<d`,
not over an externally chosen cutoff.  Its endpoint quotient is the trace-ideal exit at `u=d`.
The required successor theorem is:

```text
boundary index of the cubic source-clock lift
 = theta Kakutani escape multiplicity,
```

through a relative pairing whose normalization is forced by theta completion, with the same ideal
representative equal to the anomaly-subtracted primitive Euler remainder already proved strictly
sub-unit.  The already-proved universal survival-shift index `1` cannot serve: it is present for
every source history and therefore cannot distinguish neutral from escaping Xi copies.  No such
relative identification is claimed here.
