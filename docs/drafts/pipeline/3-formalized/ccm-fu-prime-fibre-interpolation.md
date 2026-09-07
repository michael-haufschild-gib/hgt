# CCM-FU: all-cutoff prime-fibre interpolation and packet energy

- **Stage:** 3-formalized
- **Type:** unconditional clipped source recursion, mixed energy law and copied-packet bound
- **Source:** [adaptive original-diagonal ceiling PE4](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** PE4, PE4G, SD1 and RH remain open. The complete signed mixed inner product is identified, not bounded with the sign needed for the original diagonal.

## Exact clipped homothety

Let p be prime, M any cutoff, `N=floor(M/p)`, and

`theta=(sqrt(M)-sqrt(p*N))/(sqrt(p*(N+1))-sqrt(p*N))`.

The denominator is strictly positive and `0<=theta<1`. Splitting the original time prefix into complete p-blocks and its last partial block gives, for every source index d,

`K_(pd)(M)=sqrt(p)*K_d(N)+(sqrt(M)-sqrt(p*N))*D(floor(N/d))`.

The quotient is constant on the partial block, and its square-root increments telescope exactly. The unsigned successor law is valid even at newly born and zero channels. Consequently

`K_(pd)(M)=sqrt(p)*((1-theta)*K_d(N)+theta*K_d(N+1))`.

The interpolation weight is common to every source coordinate. No last block is discarded and no approximation of the physical clock is used. If p does not divide d, Möbius multiplication supplies a minus sign for the signed channels. If p divides d, the signed pd channel vanishes because it is not squarefree.

## The entire retained field

Write `F_(M,P)(R)` for the actual fibre at remaining prime label R, with p unprocessed and absent from R. Define

`B_(M,p,P)(R)=(1-theta)*F_(N,P)(R)+theta*F_(N+1,P)(R)`.

Exact multiple reindexing and the prime-square exclusion prove

`F_(M,P)(R union {p})=-sqrt(p)*B_(M,p,P)(R)`.

The potentially repeated prime in the cofactor causes no missing term: a cofactor containing p cannot lie in the p-free retained label R, while its larger pd channel is zero. The N+1 fibre includes the newly born d=N source coefficient. Its own terminal d=N+1 coefficient is zero. Thus all births and exclusions are included.

This identity holds for every prime and cutoff, without the earlier restriction p>N. Processing p subtracts the interpolated field:

`F_(M,P union {p})(R)=F_(M,P)(R)-sqrt(p)*B_(M,p,P)(R)`.

For p<M, the complete retained-energy change is

`Q_(P union {p})(M)-Q_P(M)=-2sqrt(p)*sum_R F_(M,P)(R)*B_(M,p,P)(R)`,

over all p-free subsets of the full prime universe below M. The removed partner energy cancels the copied field's square exactly. The surviving mixed term retains its original sign and labels.

## Unconditional copied-packet budget

For any finite family T of p-free labels, put `A_R=F_(N,P)(R)` and `C_R=F_(N+1,P)(R)`. The exact interpolation energy is

`sum_T B_R^2=(1-theta)*sum_T A_R^2+theta*sum_T C_R^2-theta*(1-theta)*sum_T(C_R-A_R)^2`.

The last term is nonnegative before subtraction. Any finite family of retained labels carries at most the complete retained energy: labels outside the source prime universe vanish. Therefore

`sum_T F_(M,P)(R union {p})^2 <= p*((1-theta)*Q_P(N)+theta*Q_P(N+1))`.

This bounds the actual prime-containing packet, including overlapping-label states. It does not bound the complete merger's mixed term. Both smaller energies use the same processed set P; separate good orderings at N and N+1 would not provide this compatible state automatically. No original-diagonal bound at either cutoff is assumed.

## Lean audit

- `MobiusDivisorClippedHomothety.lean`: one definition and eight public theorems; full time-prefix representation, clipped block identity, all-index successor, clock coefficient bounds and unsigned/signed interpolation.
- `MobiusDivisorPrimeFibreInterpolation.lean`: one definition and nine public theorems; all-cutoff fibre/head/energy laws, arbitrary-label packet bound, exact interpolation defect and copied-prime energy bound.

Both leaves passed scratch and foreground `lake env lean <leaf> -o <exact olean>`. All nineteen new public declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`. No numerical premise or added axiom enters these results. Both leaves are wired once into `RHTower.lean`. No umbrella, full or dependency build ran; previously audited declarations were not re-audited.

The single global lint run reported ten unrelated concurrent modules missing umbrella imports, in the `ThetaCuspFactoredReflection`, `ThetaCuspScaleSeven`, `ThetaCuspFirstAtomScaleSeven`, `ThetaCuspSharpFiniteCooling`, `FirstAtomOddScaleSeven`, `ScaleSevenHankelPerturbation` and `LogarithmicLaplaceScoreBounds` families. Neither new CCM-FU module was flagged.
