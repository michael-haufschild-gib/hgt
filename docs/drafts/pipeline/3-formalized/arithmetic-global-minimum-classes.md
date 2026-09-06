# Global arithmetic minimum classes are determined by the tail exponent

**Stage:** 3-formalized. **Scope:** the complete global-class audit, including critical-line minimum attainment. RH remains unproved. [Frozen conjecture and mechanism sources](../1-in-progress/arithmetic-global-minimum-classes.md).

## Exact source and coefficient

Let `sigma=Re(s)>0`, `s!=1`, `u=conjugate(s)`, and retain the literal ordinary remainder

`R_s(N)=sum_(k=1..N)k^(-s)-zeta(s)-N^(1-s)/(1-s)-N^(-s)/2`,

`W_p=p^(1-s)sum_(n>=1)n^(-s)conjugate(R_s(pn))`.

Lean proves the exact first coefficient and an explicit error bound:

`|R_s(N)+s N^(-s-1)/12| <= |s(s+1)(s+2)| N^(-sigma-2)/(sigma+2)`.

The periodic kernel `({x}^2-{x})/2` has mean `-1/12`. Integrating its centered part gives a bounded periodic primitive that vanishes at every integer. Integration by parts retains the complete primitive tail and proves this estimate. It actually holds for `sigma>-1`, away from the pole.

Dominated convergence in the actual multiples sum then gives

`p^(2 sigma) W_p -> -u S_sigma/12`, where `S_sigma=sum_(n>=1)n^(-2 sigma-1)`.

In particular `A_p=p^(2 sigma) Re(W_p/[u(u+1)])` tends to `-c_s`, where

`c_s=S_sigma Re(1/(u+1))/12 > 0`.

The coefficient is derived without imposing a zero equation. The previously stated sharper `O_s(p^(-2 sigma-2))` error for `W_p` is not claimed as formalized by these modules.

## Complete global classification

For arbitrary real `a`, the existing profile is exactly

`P_a(p)=mu(p) p^(a-2 sigma) A_p`.

Products `p=2q` with odd primes `q` supply arbitrarily large moduli with `mu(p)=1`. Thus every profile has negative entries, including at nonzeros. If `a<2 sigma`, the existing uniform bound makes the profile tend to zero, so its negative global minimum is attained. If `a>2 sigma`, the profile is unbounded below along those squarefree moduli, so no global minimum is attained.

The original profiles are `X=P_1`, `Y=P_(4 sigma-1)`. Their least-minimum labels therefore obey:

| Parameter | First label | Second label |
|---|---|---|
| `sigma>1/2`, `s!=1`, whether zero or nonzero | Positive | `0` |
| `0<sigma<1/2`, whether zero or nonzero | `0` | Positive |
| `sigma=1/2` and `zeta(s)=0` | Positive | Equal to first label |

Here `0` means nonattainment, not a profile value. Least-index selection retains ties.

On the critical line, `c_s=S2/[8(t^2+9/4)]`. The existing exact arithmetic mean forces a finite `X_p<-c_s`. Since `X_q>=-|A_q|` and `-|A_q|->-c_s`, all sufficiently late terms exceed that finite value. Minimizing a finite initial segment proves attainment. This closes the earlier paper-only asymptotic-to-attainment step.

Consequently the `(0,0)` class contains no open-strip zero. At a strip zero, both labels are positive **if and only if** the zero is on the critical line.

## Scientific consequence and limit

The finite/nonattained pattern supplies no additional test distinguishing zeros from nonzeros in either open half-strip. Requiring both minima to be attained at every zero is exactly the missing location assertion in this representation; these modules do not derive it from arithmetic. The individual finite indices, minimum values, and relations between moduli remain potential data for a different constraint. Their sufficiency is unproved.

This closes the specified minimum-avoidance candidate and extracts its exact positive residue. It does not rule out other classifications or prove that no arithmetic identity can establish RH. No literature novelty claim is made. No new numerical experiment was needed for this audit.

## Lean certificate

All declarations are in `RHTower.DeletionMixedRefinement`.

| Module | Principal declarations |
|---|---|
| `EulerDeletionRemainderFirstCoefficient` | `powerSumRemainder_eq_mean_add_primitive`, `norm_powerSumRemainder_sub_mean_le`, `tendsto_powerSumRemainder_mul_endpoint` |
| `EulerDeletionModulusFirstCoefficient` | `tendsto_infiniteRemainder_scaled` |
| `ArithmeticGlobalMinimumClasses` | `exists_minimumProfile_neg`, `exists_minimumProfile_minimum_of_lt`, `minimumProfile_unbounded_below`, `rightMinimum_attained_on_line`, `arithmeticMinimumClass_strict_right`, `arithmeticMinimumClass_strict_left`, `arithmeticMinimumClass_on_line`, `not_arithmeticMinimumClass_zero_zero_at_zero`, `arithmeticMinimumClass_both_positive_iff` |

The complete scratch files and published sources passed `lake env lean`. Each new leaf passed its serialized `LEAN_NUM_THREADS=1 lake build --old <module>` audit. All three are wired into the RHTower umbrella; no full or umbrella build was run.

All 21 public declarations (18 theorems, 3 definitions) passed a separate `/tmp` `#print axioms` audit. Only `propext`, `Classical.choice`, and `Quot.sound` were reported. No added mathematical axiom or computational certificate is used.

Index and global lint verification are recorded after the final repository audit.
