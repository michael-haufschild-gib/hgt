# CCM-FU: large first-prime orientation and actual two-prime ceilings

- **Stage:** 3-formalized
- **Parent:** [bounded quotient profiles](../1-in-progress/ccm-fu-bounded-quotient-profiles.md)
- **Result:** At every sufficiently large cutoff M, every first prime p with `M<=5p` preserves all retained Möbius signs. Every distinct second prime q<M then contracts energy and meets the original ceiling. No third-step or complete-schedule claim follows.

## Exact endpoint estimates

Write `D(n)` for the literal prime-free divisor defect and `K(N)=K_1(N)` for its unit half-order channel. Its exact successor identity is

`K(N+1)=K(N)+(sqrt(N+1)-sqrt(N))D(N)`.

Analytic Euler-constant and rational logarithm bounds give `D(1)<=1/6` and `D(2)<=1/24`. Together with `sqrt(2)<=3/2` and `sqrt(3)>=1`, these prove `K(N)<=sqrt(N)/16` for N<=3.

For the fourth endpoint the same actual formulas give

`D(1)<=3861/25000`, `D(2)<=13/6250`, `D(3)<=12761/50000`.

The three positive clock increments are at most `415/1000`, `319/1000` and `268/1000`. Multiplying and adding these rational bounds proves `K(4)<=2/15`. These inequalities follow from analytic logarithm bounds and squared rational comparisons with 2 and 3; no saved channel values enter them. The exact fourth defect is nonpositive, so `K(5)<=K(4)<=sqrt(5)/15`. Consequently

`forall N<=5, K(N)<=sqrt(N)/15`.

## All clipped dilations and all cofactors

The exact interpolation of `K_p(M)` and its square-root mass has the same nonnegative weights at adjacent quotient endpoints. The endpoint bound therefore gives

`forall M,p>0, M<=5p -> K_p(M)<=sqrt(M)/15`.

The endpoint M=5p is covered by exact integer homothety; no clipped endpoint is discarded.

The exact smooth mean `a=log(2*pi)/2-gamma-1/6` satisfies `a>41/240`: the actual Stirling limit gives `log(2*pi)/2>=11/12`, while the analytic Euler-constant bound is below `139/240`. Hence `a-5/48>1/15`. The already closed complete unit coefficient band supplies a common tail with `K_1(N)>=sqrt(N)/15`.

Let T be its starting index and take `M>=4max(T,1)`. If `M<=5p`, any active child cofactor `pd` must have d<=4. Both adjacent parent quotient endpoints are then in the common unit tail. Exact interpolation gives `K_d(M)>=sqrt(M)/15`, while the child ceiling gives `K_(pd)(M)<=sqrt(M)/15`. For d>=5 the child is zero; d=0 is also covered. Thus one universal parent threshold proves

`forall p>0, M<=5p -> forall d, K_(pd)(M)<=K_d(M)`.

## Retained signs and complete two-prime energy

An original retained prime label R has oriented amplitude `K_(product R)(M)`. Processing p replaces it by that amplitude minus `K_(p*product R)(M)`. The cofactor comparison makes every such difference nonnegative. Labels containing a processed p vanish; labels containing a nonprime vanish directly from the exact source definition. Thus the assertion covers every retained label, without support omissions.

Full retained sign orientation makes every available next prime contract complete energy. The first prime already contracts the original energy. For one universal M0, every M>=M0 and distinct primes p,q<M with M<=5p therefore satisfy

`E_{p,q}(M)<=E_{p}(M)<=E_empty(M)`.

By symmetry, every two-prime ceiling failure at these parent cutoffs requires `5p<M` and `5q<M`. Combining the unit comparison with the existing universal quotient-tail bound gives thresholds M0,T such that any factor-two unit failure at M>=M0 satisfies `5p<M` and `5<=M/p<T`.

The finite parent regime, remaining middle quotient profiles, smaller-prime two-operation region and complete growing schedule remain open. This does not prove SD1 or RH.

## Verification

The complete scratch proof and exact `RHTower.MobiusDivisorLargePrimeOrientation` leaf passed `lake env lean`; only its required new olean was generated. All eight new public declarations were axiom-audited once in a separate scratch file: their dependency closures use only `propext`, `Classical.choice` and `Quot.sound`, with no added axioms or computational certificates. Formal lint passed with existing large-file warnings only. The leaf is wired once without dependency, full or umbrella builds. Card links and scoped whitespace checks passed. The saved-table reanalysis is separate numerical guidance; none of its results is a Lean premise.
