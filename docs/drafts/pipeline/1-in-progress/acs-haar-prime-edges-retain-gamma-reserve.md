# The original prime edges retain a reserve after Gamma coupling

- **ID:** acs-haar-prime-edges-retain-gamma-reserve
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Route:** ACS: full-source effectivity → Hodge index → RH.
- **Parent:** [joint signed graph payment](acs-haar-gamma-signed-graph-payment.md)
- **Target:** Prove that every actual prime-power edge remains aligned
  after its full Gamma coupling, with an explicit positive reserve, and
  sum this payment over the original finite source.

## Exact source target

Write n_a=2a+1 and n_b=m*n_a. For a>=1 and m>=3, seek

`0 <= J_ab <= log(2)*M_b/sqrt(m)`.

If Lambda(m)>0, oddness forces its underlying prime to be at least
three. Thus the original arithmetic coupling exceeds J_ab by at least
`log(3/2)*M_b/sqrt(m)`. In the already formalized ground coordinates,
the Gamma graph on these arithmetic edges should consume at most
`log(2)/log(3)` of their original divisor-square energy. Both original
pole moments have nonpositive cross entries in the oriented Haar basis;
the actual full-Weil prime-edge sign should therefore retain this reserve.

This is a proposed actual-source payment, not an assumed path
certificate. Non-arithmetic Gamma edges and the signed diagonal still
need their joint comparison; full Haar positivity is not claimed.

## Proof mechanism to complete

1. Prime-related cells have original log separation at least log(2).
   Their exact endpoints also give sqrt(m)*k(y-x)<=2 throughout the
   original rectangle.
2. Each Haar profile has zero mean and absolute integral 2*M_a.
   Centering a kernel in [0,2/sqrt(m)] at 1/sqrt(m) gives
   `J_ab <= 4*M_a*M_b/sqrt(m)`.
3. The original mass obeys `4*M_a<=log(2)` for every a>=1.
   Compare the resulting graph weight with the original divisor edge,
   and retain the nonpositive original pole cross term.
4. Formalize the exact finite-source comparison with no removed head,
   no changed kernel, and no unproved supersolution or packing input.

## Validation

No paper proof counts until every stated result passes Lean.
Use exact-file `lake --old env lean` checks, required missing dependency
oleans only, and no umbrella build. No axiom check, web search,
novelty check, or numerical experiment.
