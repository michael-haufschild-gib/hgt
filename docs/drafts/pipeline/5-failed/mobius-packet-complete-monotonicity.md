# Complete monotonicity of literal Möbius packets

- **ID:** E-PACKET-SIGN-001
- **Stage:** 5-failed, intermediate positive-moment mechanism only; Route E remains open.
- **Positive survivor:** quantitative coefficient recovery and adjacent-exponent sign laws, formalized in Lean.
- **Scientific status:** source theorems; novelty unverified; no RH proof or covariance ceiling.
- **Lean:** `GaloisForLFunctions.RHTower.MobiusPacketDifferenceSign`.
- **Parent:** [literal renewal energy attack](../1-in-progress/route-e-literal-renewal-energy-attack.md).

## Exact source and failed conjectures

For the ordinary integer cutoff, put

```
q_n = (n-1)/(n+1),
b_(N,k)(r) = sum_(1<=n<=N) mu(n)/(n+1)^r * q_n^k,
D f(k) = f(k)-f(k+1).
```

The proposed positive-moment mechanism required one global sign such that
every `D^j b_(N,k)(r)` had that sign. This is false for every `N>=2` and
every `r>=0`. It is not a rejection of all signed recurrences.

The weaker proposed descent `b_(N,k+1)(r)^2 <= b_(N,k)(r)^2` from the first
step also fails: for some `epsilon>0`, every `1<r<1+epsilon` satisfies
`b_(N,0)(r)^2 < b_(N,1)(r)^2` at all sufficiently large integer cutoffs.
The cutoff threshold may depend on `r`. This does not exclude descent after
a later packet index, nor boundedness of the complete packet energy.

## Uniform positive survivor

Let `B=sum_(n>=1) 4/(n+1)^2`, a finite nonnegative constant. Then

```
|D^(h+2) b_(N,0)(r) - 2^(-r)| <= B*(2/3)^h                 (N>=1),
|(3/2)^h D^(h+2) b_(N,1)(r) + (4/27)*3^(-r)| <= B*(3/4)^h (N>=2).
```

These estimates hold for all `r>=0` and all natural `h`. They recover two
opposite arithmetic coefficients uniformly over every ordinary integer
cutoff, without replacing the source by a prime product or omitting its tail.

Repeated differences give the exact source identity

```
D^j b_(N,k)(r)
 = sum_(1<=n<=N) mu(n)/(n+1)^r * q_n^k * (2/(n+1))^j.
```

The first detector retains `mu(1)=1`. Every remaining base is at most `2/3`.
The second kills the first coefficient through `q_1=0`, retains `mu(2)=-1`,
and gives every later base at most `3/4`. The two extra differences supply
the common summable majorant `4/(n+1)^2`. Thus at sufficiently high common
difference order the two detectors have opposite strict signs, uniformly
over `N>=2`. Either proposed global orientation contradicts one detector.

## Retained prime correction and first square increase

Write `V_N(r)=sum_(n<=N) mu(n)/n^r`, `U_N(r)=b_(N,0)(r)`, and
`d_n(r)=n^(-r)-(n+1)^(-r)`. For `N>=5` and `r>=0`, the exact nonnegative
sum `sum_(n<=N) (1-mu(n))*d_n(r)` retains the prime terms at `2,3,5` and
the squareful term at `4`. Telescoping gives

```
U_N(r) >= V_N(r)-1 + K(r),
K(r) = 2*(d_2(r)+d_3(r)+d_5(r))+d_4(r).
```

At exponent two, `K(2)=1519/3600`. The proved zeta value gives
`invZeta(2)=6/pi^2>3/5`, so `invZeta(2)-1+K(2)>1/100`.
Continuity and the admitted Möbius Dirichlet series imply

```
exists epsilon>0, forall 2<r<2+epsilon,
eventually N, U_N(r)>1/200.
```

The previous source theorem gives `U_N(r)<-1/80` eventually near `r=1`.
The exact recurrence, now formal for every packet index, is

```
b_(N,k+1)(r) = b_(N,k)(r)-2*b_(N,k)(r+1).
```

Consequently `b_(N,1)(r)<b_(N,0)(r)<0` at every sufficiently large cutoff
near `r=1`, proving the strict first square increase.

## Formal evidence and remaining obstacle

Namespace `RHTower.MobiusPacketDifference`:

- `unitDetector_error`, `primeDetector_error`, `difference_packet`;
- `unitDetector_eq_difference`, `primeDetector_eq_difference`;
- `eventually_opposite_detector_signs`, `no_completely_monotone_orientation`;
- `packet_zero_eq_shiftedMoment`, `packet_succ_eq_adjacent_orders`;
- `eventually_first_packet_square_increases`.

Namespace `RHTower.MobiusRenewalEnergy`:

- `shiftedMoment_lower_primeCorrection`;
- `eventually_shiftedMoment_positive_near_two`.

The entire proof passed `lake env lean /tmp/route_e_packet_combined.lean`
without warnings. The production module is wired into `RHTower.lean`.
Final targeted audit and lint status are recorded on the parent card.

The no-go's strongest positive survivor is the uniform quantitative recovery
of opposite source coefficients, together with the full retained-prime
moment lower bound and exact recurrence. Both paper proofs and Lean proofs
are closed. No upper bound for the signed moving-cusp covariance follows.
The full packet expansion and the adjacent-exponent mixed-energy calculation
on the parent card remain paper work; this leaf does not formalize them.
