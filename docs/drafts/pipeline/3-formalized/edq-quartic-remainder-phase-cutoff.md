# Exact quartic remainder and a uniform arithmetic phase cutoff

- **Stage:** 3-formalized
- **Type:** unconditional source theorems; [BRIDGE]
- **Modules:** `EulerDeletionQuarticRemainder`, `ArithmeticRemainderPhaseCutoff`
- **Namespace:** `RHTower.DeletionMixedRefinement`

RH remains unproved. The result gives an explicit joint height/cutoff region for the literal remainder, without a zero equation or an assumed sign law. It does not control the exceptional initial terms or prove the proposed linear cutoff.

## Literal source and exact correction

For `s=sigma+i*t`, put

`R_s(N)=sum_(j=1..N)j^(-s)-zeta(s)-N^(1-s)/(1-s)-N^(-s)/2`,

`g_s(N)=N^(-s)*conjugate(R_s(N))/[conjugate(s)*(conjugate(s)+1)]`.

The latter is the existing `normalizedWeightedRemainder`, not a fitted or independently chosen model. For positive sigma and positive integer N, it equals `N^(-s)*T_conjugate(s)(N)`, where `T_s(N)` is the actual Bernoulli tail with kernel `b(x)=(fract(x)^2-fract(x))/2`.

The centered kernel's primitive is exactly

`P(x)=fract(x)^3/6-fract(x)^2/4+fract(x)/12`.

The next primitive is

`H(x)=fract(x)^2*(1-fract(x))^2/24`.

Lean proves `H'=P` at every real point, including integer joins, `H(N)=0`, and `0<=H<=1/384`. Right derivatives and the fundamental theorem of calculus identify the integral primitives before any half-line integration by parts is used.

For `sigma>-1` and integer `N>=1`, define `U_s(N)=integral_(N..infinity)H(x)*x^(-s-4)dx`. Then

`T_s(N)=-N^(-s-1)/(12*(s+1))+(s+2)*(s+3)*U_s(N)`,

`|U_s(N)|<=N^(-sigma-3)/(384*(sigma+3))`.

Absolute integrability and both boundary limits are proved. The ordinary power-sum identity follows by multiplying by `s(s+1)` when `s!=1`.

## Joint phase bound

For `sigma>0`, `s!=1`, and `N>=1`, the exact normalized remainder satisfies

`|N^(2*sigma+1)*g_s(N) + 1/[12*(conjugate(s)+1)]|`

`<= |s+2|*|s+3|/[384*(sigma+3)*N^2]`.

The leading imaginary part is `-t/[12*|s+1|^2]`. Therefore `Im(g_s(N))<0` whenever `t>0` and

`|s+2|*|s+3|*|s+1|^2 < 32*(sigma+3)*t*N^2`.

Throughout `0<sigma<=1` and `t>=1`, the simple sufficient condition is

`t^3<=N^2`.

The proof uses `|s+1|^2<=5t^2`, `|s+2|^2<=10t^2`, `|s+3|^2<=17t^2`, and `2|s+2||s+3|<=|s+2|^2+|s+3|^2`. This bounds the criterion's left side by `135t^4/2`, strictly below `96t^4`, while its right side is larger than `96t^4`. No numerical evaluation is used.

## Exact scope

The capstone `normalizedWeightedRemainder_im_neg_of_height_cube` quantifies over every parameter and cutoff in that region. It strengthens fixed-parameter eventual negativity to an explicit simultaneous bound. It is weaker than conjecture R's proposed `t<2*pi*N`, which remains unproved. Neither the complete-prefix conjecture B2 nor the undamped-clock conjecture C is asserted.

At a high zero the unit term lies outside this region. The existing exact unit identity retains the full normalized zeta discrepancy and its signed critical-line displacement. A new source law controlling the exceptional head remains necessary to derive RH. No route is retired by this result, and no literature-wide novelty is claimed.

## Declarations and verification

The first module has eleven public declarations; the second has five. Principal results are `bernoulliTail_eq_mean_add_quartic`, `norm_quarticPrimitiveTail_le`, `norm_normalizedWeightedRemainder_scaled_sub_mean_le`, `normalizedWeightedRemainder_im_neg_of_quartic_bound`, and `normalizedWeightedRemainder_im_neg_of_height_cube`.

The combined scratch proof and both separate source checks pass `LEAN_NUM_THREADS=1 lake env lean` without warnings, including the scratch API-name check. Serialized final audits `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionQuarticRemainder` and `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ArithmeticRemainderPhaseCutoff` pass, rebuilding only those leaves. All sixteen public declarations were audited through `/tmp/edq_quartic_final_axioms.lean`; each uses only `propext`, `Classical.choice`, and `Quot.sound`. There is no added axiom, placeholder, or computational certificate. The audit output is `/tmp/edq_quartic_axioms.log`. Subsequent source cleanup removes only trailing whitespace, with the token sequence unchanged.

The corpus index is refreshed and retrieves the capstone. Global `python3 scripts/formal_tools.py lint --check-generated` fails only on two unrelated modules missing umbrella imports: `RHTower.ThetaCuspModularCompactTube` and `HTGeometry.PolynomialODEJetRankThreeCompactExpansion`. Existing large-file warnings also remain. Output is `/tmp/edq_quartic_lint.log`; global lint is not claimed to pass. The scoped tracked-file whitespace check passes. Every owned Lean process completed.

Both modules are wired into `RHTower.lean`. No full or umbrella build is used.

Related: [proof derivation and continuing RH goal](../1-in-progress/edq-quartic-remainder-phase-cutoff.md), [unchanged linear-cutoff conjecture](../1-in-progress/arithmetic-successor-phase-threshold.md), [complete-prefix and clock conjectures](../1-in-progress/arithmetic-log-phase-blocks.md).
