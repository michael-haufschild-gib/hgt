# Prime--archimedean Bernstein Dirichlet dissipation law

- **ID:** `prime-arch-bernstein-dirichlet-dissipation-law`
- **Status:** 3 -- formalized
- **Classification:** `[BRIDGE; RH-BEARING SPECIALIZATION]`

## Claim

For a real moment functional, let
\[
 a_{n,i}=\ell(B_{n,i}),\qquad
 \Pi_n=\sum_{i=0}^{n}a_{n,i}^2,
\]
and define the degree-elevation Dirichlet dissipation
\[
 \mathfrak D_n=
 \frac1{n+1}\sum_{i=0}^{n}(n+1-i)(i+1)
   (a_{n+1,i}-a_{n+1,i+1})^2.
\]
Then
\[
 (n+2)\Pi_{n+1}-(n+1)\Pi_n=\mathfrak D_n\ge0.
\]
Consequently
\[
 (n+1)\Pi_n=\Pi_0+\sum_{k=0}^{n-1}\mathfrak D_k.
\]

For the endpoint prime--archimedean source, RH is therefore equivalent to one fixed linear
cumulative-dissipation bound recurring at arbitrarily large degrees:
\[
 \mathrm{RH}
 \iff
 \exists C\;\forall N\;\exists n\ge N,
 \qquad \sum_{k<n}\mathfrak D_k\le C(n+1).
\]
Under failure of RH, the cumulative mean dissipation tends to positive infinity.

## Proof mechanism

Bernstein degree elevation gives
\[
 a_{n,i}=\alpha_{n,i}a_{n+1,i}+\beta_{n,i}a_{n+1,i+1},
\]
where
\[
 \alpha_{n,i}=\frac{n+1-i}{n+1},\qquad
 \beta_{n,i}=\frac{i+1}{n+1}.
\]
The row identity
\[
 (n+1)(\alpha x+\beta y)^2
 +\frac{(n+1-i)(i+1)}{n+1}(x-y)^2
 =(n+2)(\alpha x^2+\beta y^2)
\]
is exact. Summing over `i` uses the fact that the two elevation columns have total weight one.
The telescoping formula follows by induction. The RH specialization combines this identity with
the proved cofinal-boundedness/purity-divergence dichotomy.

## Exact open core

Prove the cofinal linear bound from the prime--Gamma source without importing a divisor-positive
or reflection-positive realization. Reflection positivity supplies the bound only after the
RH-bearing Gram condition has already been established.

## Formalization target

`formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinDirichletDissipation.lean`

Master integration:

`formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinNarrowSectorDissipationMaster.lean`

## Gates

- [x] Exact algebraic identity derived on paper
- [x] Existing degree-elevation theorem located
- [x] General Lean balance law
- [x] Endpoint RH specialization
- [x] Targeted axiom and placeholder audit
- [x] Manuscript integration
