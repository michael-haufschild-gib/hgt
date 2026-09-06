# Arithmetic minimum classes: the missing complex constraint

- **Stage:** 1-in-progress
- **Objective:** determine whether the actual real minimum data and its exact arithmetic balance supply an off-line exclusion, or identify precisely what additional source information is needed.
- **Starting evidence:** `ArithmeticZeroMinimumClasses` and the actual absolute Möbius inverse. The two profiles are formed from the real part of the same normalized complex remainder. No RH proof or new architecture is assumed.

**Outcome:** G, H, and I are proved in Lean on the actual source. The projected recognition/exclusion conjecture F fails: every actual strip zero has arbitrarily nearby nonzero projected witnesses and forces an off-line nonzero projected witness. The negative mean, negative entries, and minimum attainment below the decay exponent already follow from the projected balance without a zero assumption. E supplies only the generic tilt order; the actual zero equation has not supplied a second attained minimum or an opposing order. [Formal certificate and exact scope](../3-formalized/arithmetic-minimum-phase-completeness.md).

## Frozen conjectures and attacks

Write `u=conjugate(s)`, `D=u(u+1)`, `B_p=mu(p)W_p/(pD)`, and `C(s)=sum B_p`. The existing profiles are `X_p=p^2 Re(B_p)` and `Y_p=p^(4 Re(s)) Re(B_p)`.

**E — an opposing minimum order can be extracted from the signed balance.** At a strict-right zero, a possible exclusion would compare the two minimizing labels in opposite directions. First prove the direction forced by the exact tilt `Y_p=p^(4 Re(s)-2)X_p`. Then try to derive the opposite direction from the negative weighted balance, keeping track of exactly where the zero equation is used. A generic toy model may refute implication from the balance alone; it cannot refute a theorem about actual zeta zeros.

**F — the real arithmetic balance suffices to recognize zeros.** In the open strip, conjecture that

`Re(C(s))=-Re(1/[u(1-u)])/2`

forces `zeta(s)=0`. Attack this on the actual source, not on a replacement sequence. Derive the full complex identity before computing. If it reduces the proposed condition to `Re(zeta(s)/[s(s+1)])=0`, search on the specified Runpod for off-line nonzeros satisfying that projected equation near known critical-line zero approximations. Approximate roots will be labeled numerical evidence, not Lean counterexamples.

**G — the omitted complex balance identifies the exact extra constraint.** Independently conjecture the absolutely convergent identity

`C(s)=-1/[2u(1-u)]-conjugate(zeta(s))/D`.

At a zero its imaginary part should be

`Im(C(s))=Im(s)(2 Re(s)-1)/(2 |u(1-u)|^2)`.

Prove or reject these equalities from the existing inverse. Do not call the requirement that the last quantity vanish a new producer: an arithmetic proof of that vanishing would still be missing.

## Experimental protocol

For the first 24 critical-line zero approximations, solve the projected real equation at real parts 0.45 and 0.55 by continuation from the zero height. Retain nonconvergent cases and multiple-root warnings. Recompute at higher precision with a separate root method for selected witnesses. Evaluate actual remainder profiles with varied direct-head sizes and Euler–Maclaurin tail orders; compare finite-grid minimum labels and record the full complex residual. All numerical work runs on the specified Runpod. No computed result enters a Lean proof.

## New conjecture exposed by the projection experiment

**H — unavoidable nearby nonzero points with exact projected balance.** For every zeta zero `rho` in the open strip and every positive radius, there is a point `s` in that radius and in the strip where the real arithmetic balance holds but `zeta(s) != 0`. This is stronger than one numerical counterexample to F and is frozen independently before its Lean proof. It does not assert that each witness is off the critical line.

Paper proof: `f(s)=zeta(s)/(s(s+1))` is holomorphic on the connected open strip. It is nonconstant, since `f(rho)=0` but the coefficient-side real-strip negativity theorem gives `f(1/2) != 0`. By the open mapping theorem, the image of any open strip neighborhood of `rho` contains a disk about zero. A small nonzero purely imaginary point in that disk has a preimage `s`. Then `Re(f(s))=0` but `f(s) != 0`; the already derived exact inverse identifies these with the projected balance and nonvanishing of zeta. This paper proof has no numerical premise and no simplicity assumption on the zero.

The initial numerical scan recorded 41 converged targets and 7 failures. Some converged secant paths jump to distant roots, including repeated arrivals at the same root; those must not be reported as 41 local continuations or 41 distinct witnesses. The verification report must retain this distinction.

**I — an off-line nonzero point with exact projected balance follows from any strip zero.** Freeze this separately from H. Open mapping at a zero gives an interior point where `Re(f)>0`. Openness permits choosing such a point off the critical line. At the real-axis point with that same real part, the coefficient-side sign theorem gives `Re(f)<0`. The intermediate value theorem on that vertical line gives an off-line point with `Re(f)=0`. If its zeta value is nonzero, it is the desired witness. If it is a zeta zero, apply H in a ball too small to meet the critical line. This proves the existence claim from any given strip zero without numerical input and without assuming RH. It does not locate the witness, classify its global minima, or prove that every nearby projected witness lies off the line.

## Corpus mechanisms inspected

Corpus searches covered minimum order, tilt response, signed boundary cancellation, multiples inversion, arithmetic skew, support jets, periodic averaging, and Bernoulli dilation. The finite tilt response module shows how a common rescaling can manufacture an order relation. The absolute multiples inverse gives the actual complex source identity. Unrestricted opposite-sign transport has an existing corpus warning: minimizing unmatched mass can reproduce the original signed imbalance without producing cancellation. These mechanisms motivate the attacks; they supply no unproved RH hypothesis.

The later `open mapping` corpus search exposed `HTGeometry.CompositionOrderTransfer.eq_zero_of_eq_zero_on_range` and its actual use of `AnalyticOnNhd.is_constant_or_isOpen`. Reading that proof and the current mathlib open mapping statement led to H. The `zeta real negative` search exposed `ZetaRealStrip.riemannZeta_real_strip_neg`, whose proof uses the paired eta coefficients; it supplies the real anchor for I. No functional equation or spectral mechanism enters the new proof.

Exact query strings used with the research tool include `minimum monotone tilt`, `arithmetic sign variation`, `remainder asymptotic`, `tilt order`, `minimum rigidity`, `multiples inversion`, `signed cancellation boundary`, `minimum envelope`, `arithmetic skew`, `sum imaginary remainder`, `bernoulli dilation`, `multiples kernel integral`, `bernoulli mean zero`, `periodic integral asymptotic`, `open mapping`, and `zeta real negative`. Actual statements and proof bodies were inspected with `rg` and bounded reads. These are mechanism searches, not an exhaustive corpus or literature novelty claim.

## Remaining source problem

The imaginary arithmetic sum at a zero is now exactly `Im(s)(2 Re(s)-1)/(2 |u(1-u)|^2)`. An independently proved vanishing law would exclude off-line zeros. The displayed identity itself does not prove that law. Other real constraints could also supply the missing information; this result does not prohibit real-valued methods or prove every possible minimum classification insufficient. It rules out the particular projected balance, together with consequences already derived from that balance, as the full location argument.

The [Runpod report](../2-fully-proven/computations/arithmetic-minimum-phase-completeness/REPORT.md) records actual projected nonzeros, solver jumps and failures, independent 100-digit checks, and the distinction between finite-grid and global minimum labels.
