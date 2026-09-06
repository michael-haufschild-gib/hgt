# Arithmetic minimum balance loses a necessary complex component

- **Stage:** 3-formalized
- **Scope:** exact source reconstruction and rejection of the projected balance as a location test; RH remains unproved
- **Research:** [frozen conjectures and paper proofs](../1-in-progress/arithmetic-minimum-phase-completeness.md)

## Exact statements

Use the actual arithmetic remainder `W_p` from [the minimum-class construction](arithmetic-zero-minimum-classes.md). Put `u=conjugate(s)`, `D=u(u+1)`, `B_p=mu(p)W_p/(pD)`, `C(s)=sum B_p`, and `Q(s)=-1/[2u(1-u)]`. In the open strip,

`C(s)=Q(s)-conjugate(zeta(s)/(s(s+1)))`.

The sum is absolutely convergent by the existing arithmetic inverse. Consequently:

- The full complex discrepancy `C-Q` vanishes exactly at zeta zeros.
- The real arithmetic balance `Re(C)=Re(Q)` is exactly `Re(zeta(s)/(s(s+1)))=0`.
- The omitted discrepancy is `Im(C-Q)=Im(zeta(s)/(s(s+1)))`.
- At a zeta zero, `Im(C)=Im(s)(2 Re(s)-1)/(2 |u(1-u)|^2)`.

The last equality exposes the location-sensitive component. It does not prove its vanishing.

## Proved failure on the actual source

For **every** zeta zero `rho` in the open strip and **every** positive radius, Lean proves there is an `s` within that radius, still in the strip, satisfying the exact real arithmetic balance with `zeta(s) != 0`. No simplicity assumption is used. The theorem does not assert that every such nearby witness lies off the line.

Lean also proves that **any given strip zero forces an off-line nonzero point in the strip satisfying the exact real balance**. This second theorem does not prescribe its height or distance from the given zero. Neither theorem uses a computed zero or assumes RH. They are statements quantified over the actual zeros; this module does not separately formalize the existence of a strip zero.

Proof: the holomorphic function `f(s)=zeta(s)/(s(s+1))` is nonconstant on the strip, since it vanishes at the supplied zero but is nonzero at `1/2` by the coefficient-side real-strip sign theorem. Analytic openness supplies a nonzero purely imaginary image in every neighborhood of the zero. Its preimage proves the first assertion. For the second, openness also supplies a point where `Re(f)>0`, which can be chosen off the line. At the real-axis point with the same real part, `Re(f)<0`. The intermediate value theorem on the vertical line gives an off-line point where `Re(f)=0`. If that point is a zero, apply the first assertion inside a ball that misses the critical line; otherwise it is already the required nonzero witness.

## Positive constraints retained by the failed condition

The real balance alone, without a zeta-zero assumption, gives the exact negative weighted mean of every profile `P_a`, a negative profile entry, and negative minimum attainment when `a<2 Re(s)`. Thus these previously used consequences do not restore the discarded component.

For the same source and any positive modulus,

`P_b(p)=p^(b-a) P_a(p)`.

If `a<b` and the two profiles attain negative minima at `p` and `q`, then `p<=q`. This order law holds before imposing a zero or a balance condition. It supplies no opposite inequality from the actual zero equation.

## Lean certificate

Module: `GaloisForLFunctions.RHTower.ArithmeticMinimumPhaseCompleteness`.
Namespace: `RHTower.DeletionMixedRefinement`.

| Claim | Declaration |
|---|---|
| Full source identity | `tsum_minimumBalanceTerm_eq` |
| Full discrepancy identifies zeros | `minimumComplexDefect_eq_zero_iff` |
| Exact information retained by the real balance | `real_minimum_balance_iff` |
| Omitted imaginary discrepancy | `minimumComplexDefect_im_eq` |
| Zero-specific imaginary boundary | `tsum_minimumBalanceTerm_im_at_zero` |
| Weighted mean without a zero assumption | `tsum_minimumProfile_div_weight_of_real_balance` |
| Negativity and attainment without a zero assumption | `exists_minimumProfile_neg_of_real_balance`, `negativeMinimum_attained_of_real_balance` |
| Generic minimum order under a power tilt | `minimumProfile_minimum_order` |
| Nonzero projected witnesses near every zero | `exists_nearby_nonzero_real_minimum_balance` |
| Off-line nonzero projected witness from any strip zero | `exists_offline_nonzero_real_minimum_balance_of_zero` |

The complete scratch file and published source passed `lake env lean`. The final serialized `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticMinimumPhaseCompleteness` passed; only the new leaf was built. The leaf is wired into `GaloisForLFunctions.RHTower`; no full or umbrella build was run.

All 20 public declarations (16 theorems and 4 definitions) were audited by `#print axioms` in a separate scratch file. Only `propext`, `Classical.choice`, and `Quot.sound` were reported. No added mathematical axiom or computational certificate is used. The corpus index was refreshed and retrieves the off-line witness theorem. All owned Lean and Runpod processes completed; the remote experiment cleanup check returned an empty list.

The global `scripts/formal_tools.py lint --check-generated` gate passed with exit code 0.

## Limits

This rejects the projected balance as a sufficient zero or location test. It does not reject every arithmetic classification, every real-valued method, or a stronger class-specific constraint. The existence proofs do not prescribe the global minimum labels of the nonzero witnesses. [Runpod diagnostics](../2-fully-proven/computations/arithmetic-minimum-phase-completeness/REPORT.md) concern finite-grid labels and are separate from the proof.

The missing RH step remains an independent arithmetic law that excludes off-line zeros in the remaining classes. Requiring `Im(C)=0` at every zero would supply the missing location constraint, but this module neither proves that requirement nor treats its exact rational expression as a producer.
