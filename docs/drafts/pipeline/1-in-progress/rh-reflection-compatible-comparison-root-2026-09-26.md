# Reflection-compatible comparison after the Cauchy reserve obstruction

- **ID:** RH-REFLECTION-COMPATIBLE-COMPARISON-ROOT-20260926
- **Stage:** 1-in-progress
- **Type:** [BRIDGE] falsifiable source-comparison candidate, not a universal-law claim
- **Owner:** root
- **Parent:** `rh-full-theta-coercivity-audit-root-2026-09-26.md`

## Frozen C9

Let Phi be the complete source and K its exact tail first-moment kernel. Put
`q(x)=exp(2x)+exp(-2x)` and `H(x,y)=Phi(x)*Phi(y)/(q(x)+q(y))`.
Candidate: there exists c>0 such that Q_K>=c*Q_H for every finite real node and
coefficient family. This would supply the missing semidefinite source sign.
No proof or RH claim is assumed.

Why test it: (i) the C6 Cauchy mechanism is genuinely positive; (ii) C8 proves
its oriented scale gives an impossible incoming envelope; (iii) exact source
and kernel reflection require both ends to be retained; (iv) the proved
outgoing/incoming diagonal scales are compatible with H at both infinities.
Replacing the oriented scale by its reflection orbit invariant is a real change
in the comparison geometry. These observations do not imply the conjecture.
The exact uniform comparison is the unoccupied and risky assertion.

## Interrogation

- What does the proof need to know about theta? Any successful estimate must
  use the complete modular source; generic positivity/evenness/log-concavity
  countermodels already exist.
- What is invariant? q(-x)=q(x); H is separately even. K is jointly reflection
  invariant, with both even and odd sectors. The odd sector must still be
  nonnegative: the reference kernel contributes zero there.
- What was being removed? The incoming end. Keep it as part of the scale.
- Is this the right problem? It tests the exact all-rank sign with a metric
  surviving C8. Do not count construction of H or fixed-rank checks as proof.
- Closest parent: Cauchy Gram positivity plus analytic tail locality. This is
  known framework plus a new source inequality, so classify it [BRIDGE], not
  a primary universal conjecture.

## Plan and falsifiers

1. Audit exact reflection quotient identity and the reference Gram form.
2. Attack low-order, confluent, reflected, and complex-analytic constraints
   symbolically, with no numerical experiment.
3. Prove the comparison or find a precise obstruction; preserve the strongest
   positive invariant exposed by any failure.
4. Reassess the whole route. A plausible diagonal envelope is not a source
   sign producer.

## Charged-cusp falsification (paper and Lean proof closed)

Set eps=N^(-2), Q=eps+2i, z=log(Q)/2. Then exp(2z)=Q and the
theta parameter is -2+i*eps. Every arithmetic phase is exactly one. Writing
S_k(eps)=sum n^k exp(-pi*eps*n^2), the literal source series gives

    exp(-z/2)*Phi(z)=4*pi^2*Q^2*S_4(eps)-6*pi*Q*S_2(eps).

For eps<=1 its real part is <=-12*pi^2*S_4(eps). The block N<=n<2N
gives S_4(N^(-2))>=N^5*exp(-4*pi). Thus |Phi(z)|^2>=C*N^10.
Also Re(q(z))=eps+eps/(eps^2+4), so H(z,z)>=C'*N^12.

The required upper bound is elementary, but the existing Gaussian-power
bound has the wrong exponent. Integral comparison plus
t^k/k!<=exp(t) gives, for a>0 and k>=1,

    sum n^(2k)*exp(-a*n^2)
      <=k!*(2/a)^k*sqrt(2*pi/a)/2.

Applied to z+s this bounds |Phi(z+s)| by C*N^5*exp(-s/2).
Hence the actual source L2 section has squared norm O(N^10), including
its linear weight. Its indefinite diagonal is therefore O(N^10), whereas
the reflected Cauchy diagonal is bounded below by C'*N^12.

For a fixed cusp point use B=conj(q(z)). The analytic scalar feature
Phi(w)/(q(w)+B) has no pole in the strip, and the complex Cauchy Schur
complement gives H >= 2*Re(B)*h_B*h_B^*. This avoids constructing a new
infinite-dimensional reference realization. The existing analytic locality
theorem forces a finite negative comparison packet on every
real tail. Factors of two follow the established source realization:
its indefinite Gram is 2*K.

**Whole-route implication:** matching reflection and both real
diagonal scales does not repair the comparison. A surviving reference must
also respect charged-cusp boundary growth. This does not show K is negative
and does not decide RH. The positive survivor to extract is the precise
complex boundary admissibility inequality for any valid source comparison.

## Exact killing theorem and dependency closure

`ThetaCuspBoundaryAudit.exists_finite_negative_reflected_reserve` proves:
for every real a and c>0 there are finite real x_i>a and b_i with
`sum_ij b_i*b_j*(K_Phi(x_i,x_j)-c*H(x_i,x_j))<0`.

The three named leaf builds pass:

1. `ThetaCuspChargedBoundaryGrowth`: integral comparison, sharp Gaussian
   exponent, exact charged phase, finite-block lower bound, horizontal upper bound.
2. `ThetaTailReflectedBoundaryObstruction`: the actual complex diagonal is
   `J(z,z)=4*integral_(s>0) (Re(z)+s)*|Phi(z+s)|^2`. It is at most
   `24*486^2*N^10` at z_N. The comparison contribution `|Phi(z_N)|^2/Re(q(z_N))`
   is at least `(12*pi^2*exp(-4*pi))^2*N^12/2`. Thus `J-2cH` has a negative diagonal.
3. `ThetaTailReflectedCauchyObstruction`: the half-plane Cauchy Gram and
   Hilbert projection give the exact complex rank-one lower bound. For
   B=conj(q(z_N)), the analytic feature Phi/(q+B) attains the required diagonal.
   Closed-span compression and accumulating real-tail samples transport the
   negative direction. Real/imaginary splitting and finite enumeration finish.

No off-line zero, source sign hypothesis, or numerical experiment is used.
The unsubtracted K_Phi sign remains undecided.

## Strongest positive survivor

**Complex boundary admissibility:** a scalar analytic comparison holding for
every finite complex coefficient packet on a real tail necessarily holds at
every complex point of the strip, against the exact J diagonal.
`scalar_boundary_admissibility` formalizes that statement.

**Quantitative charged-cusp floor:** write A=12*pi^2*exp(-4*pi), D=24*486^2.
Any positive rates u_N satisfying `c*|Phi(z_N)|^2<=u_N*J(z_N,z_N)` must obey
`u_N>=c*A^2/D` for every N>=1. This follows by sandwiching both sides between
their proved N^10 bounds and cancelling N^10. Exact Lean theorem:
`chargedPoint_boundary_rate_floor`.

This is a new admissibility constraint beyond reflection and real asymptotics.
Nonvanishing boundary rate is necessary in this test; sufficiency is open.
The stronger conjecture J(z_N,z_N)/|Phi(z_N)|^2->0 is not established by these
bounds. It would require an integrated estimate retaining arithmetic phases.

## Verification and optimization gate

- Scratch proofs and all three named leaf builds pass.
- All three modules wired into the umbrella.
- 44 public theorem axiom reports and final generated-file lint pending.
- User requests proof optimization at default heartbeat limits. A per-module
  compiler profile is being measured before changing proof scripts; no
  heartbeat or recursion-depth override occurs in these leaves.

### Measured compiler baseline (default heartbeat limits, one worker)

`lake env lean -j1 --profile` on exact scratch copies:

| Module | Total wall time | Import | Tactic execution | Typeclass inference |
|---|---:|---:|---:|---:|
| ThetaCuspChargedBoundaryGrowth | 12.59 s | 5.86 s | 0.629 s | 1.86 s |
| ThetaTailReflectedBoundaryObstruction | 7.69 s | 4.18 s | 0.320 s | 0.766 s |
| ThetaTailReflectedCauchyObstruction | 12.86 s | 8.09 s | 0.438 s | 1.40 s |

The last module imports the complete C8 asymptotic graph solely for a generic
augmented Hermitian form. Remove that dependency through a lower-level shared
form, retaining the existing C8 public API. Profile the Gaussian proof's
unrestricted nonlinear searches before replacing them. Detailed artifacts:
`/tmp/rh-c9-profile-before.json`, `/tmp/rh-c9-before-*.log`.
