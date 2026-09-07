# CCM-FU: exact retained-source recursion and orientation reversal

- **Stage:** 3-formalized
- **Type:** unconditional source homothety, mixed energy identity and cofinal orientation reversal
- **Source:** [adaptive original-diagonal ceiling PE4](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** PE4, PE4G, SD1 and RH remain open. The recursion identifies the signed arithmetic comparison; it does not prove its required bound.

## Full retained-fibre copy

Write `F_(M,P)(R)` for the literal source retained at cofactor label R after processing P. For a prime p>N with p unprocessed, every source label divisible by p at cutoff pN is uniquely p*d with d<=N. The cofactor is coprime to p. Exact channel homothety and prime-factor bookkeeping give, whenever p is absent from R,

`F_(pN,P)(R union {p})=-sqrt(p)*F_(N,P)(R)`.

This is a copy of the entire retained source, with its original arithmetic weights. It includes zero and terminal coefficients and uses no asymptotic replacement. Processing p therefore gives

`F_(pN,P union {p})(R)=F_(pN,P)(R)-sqrt(p)*F_(N,P)(R)`

for every p-free retained label R; all labels still containing p disappear. The head is the case R empty.

## Exact mixed energy update

For N>=2, let U be the primes below pN with p removed. Splitting the full cofactor cube into labels with and without p gives

`Q_(P union {p})(pN)-Q_P(pN)=-2sqrt(p)*sum_(R subset U) F_(pN,P)(R)*F_(N,P)(R)`.

The square of the reflected copy cancels exactly with the removed p-containing fibre energy. The complete mixed inner product survives. No absolute values, sign assumption or endpoint bound replace it. This identity is proved at the exact integer dilation anchors pN with p>N; a general nonintegral quotient would additionally retain the clipped terminal block.

## Positive isolated fibres after smaller-prime processing

If P contains every prime below N, the smaller source is concentrated at its empty label. The retained singleton at p is then

`F_(pN,P)({p})=-sqrt(p)*S(N)`.

The already analytic seven-cutoff bounds prove `S(7)<0`. Taking P to be the primes below seven, namely2,3,5, gives a strictly positive singleton at every cutoff7p with prime p>7. These positive fibres exceed every fixed real bound beyond every cutoff, by square-root growth and the infinitude of primes. Processing that prime strictly increases the retained head.

The original prime coefficients are nonpositive by unsigned source positivity. Their retained orientation therefore need not survive earlier mergers. A blanket nonpositive-singleton extension of the late-prime rule is false for the actual source, cofinally. The positive survivor is the exact full-fibre recursion and its mixed energy law. The [late-prime endpoint theorem](ccm-fu-late-prime-block-endpoints.md) retains its stated common-sign, isolated-band scope.

## Lean audit

- `MobiusDivisorPrimeFibreHomothety.lean`:8 public theorems; full-interval fibre representation, complete prime-fibre copy, singleton copy, full smaller-source merging, scalar landing, every-fibre and head updates, and exact mixed energy update.
- `MobiusDivisorRetainedPrimeOrientation.lean`:6 public theorems; negative complete source at seven, its exact prime copy, positive retained singleton, cofinal unbounded positive fibres, failure of blanket retained-prime nonpositivity and strict head increase.

Both leaves passed scratch checks and foreground `lake env lean <leaf> -o <exact olean>`. All14 new public theorems were axiom-audited once, with only `propext`, `Classical.choice`, and `Quot.sound`. No experimental result, added axiom or unproved source premise enters these laws. Both leaves are wired once into `RHTower.lean`; no umbrella or dependency build was run.

Global formal lint was run once. It found ten unrelated concurrent modules missing umbrella imports, in the `ThetaCuspEffective` family and two `HTGeometry` leaves. Neither new CCM-FU leaf is flagged.
