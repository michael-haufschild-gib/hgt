# Semilocal all-even Jacobi--prolate residue tower

- **ID:** semilocal-all-even-jacobi-prolate-residue-tower
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean 4)
- **Scientific status:** CANDIDATE NEW SCIENTIFIC KNOWLEDGE, provisional pending independent review
- **Lean core:** `formal/GaloisForLFunctions/RHTower/SoninSemilocalJacobiTransform.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninSemilocalJacobiOrthonormal.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninSemilocalFinitePrimeMeasure.lean`, and
  `formal/GaloisForLFunctions/RHTower/SoninSemilocalJacobiResidueCorollaries.lean`
- **Parent sources:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Sections 3 and 4.3; Connes--Consani--Moscovici,
  *On q-series and the moment problem associated to local factors*, arXiv:2403.01247

## Statement

Let

`dmu_infinity(s)=(2 pi)^(-3/2)|Gamma(1/4+i s/2)|^2 ds`

and let `p_n^infinity` be its orthonormal polynomial of degree `n` with positive leading coefficient.
For a finite nonempty set `P` of distinct primes, put

`G_P(s)=prod_(p in P)|1-p^(-1/2)exp(i log(p)s)|^(-2)`,

`dnu_P(s)=G_P(s)dmu_infinity(s)/(int G_P dmu_infinity)`.

Then for every `k>=1`,

`(-1)^k int p_(2k)^infinity(s) dnu_P(s)>0`.                (1)

Thus adjoining any nonempty finite prime set gives a nonzero ground-state component of every positive
even archimedean Jacobi mode, with a rigid alternating sign.

Let `J_P` be the identity on polynomial functions from the archimedean cyclic spectral model to the
`P`-semilocal one, and let `N_infinity,N_P` be the two orthogonal-polynomial number operators. Then

`(-1)^(k+1)
 <p_0^P,(N_PJ_P-J_PN_infinity)p_(2k)^infinity>_P>0`.       (2)

For the source formal prolate family `W_(lambda,P)=-D^2+lambda^2N_P`, multiplication by `D^2`
intertwines `J_P`, so for every `lambda>0`,

`(-1)^(k+1)
 <p_0^P,(W_(lambda,P)J_P-J_PW_(lambda,infinity))p_(2k)^infinity>_P>0`.  (3)

The case `k=1` gives the normalized first-Jacobi contraction

`0<a_0(P)^2=int s^2 dnu_P(s)<1/2=a_0(empty)^2`             (4)

and the explicit positive residue

`<p_0^P,(N_PJ_P-J_PN_infinity)p_2^infinity>_P
 =2(1/2-a_0(P)^2)/sqrt(3/2)>0`.                            (5)

## Exact archimedean transform law

The characteristic function is

`phi(t)=int exp(i t s)dmu_infinity(s)=(cosh t)^(-1/2)`.

The archimedean Jacobi recurrence is

`s p_n^infinity=a_(n-1)p_(n-1)^infinity+a_n p_(n+1)^infinity`,

`a_n=sqrt((n+1/2)(n+1))=sqrt((2n+1)(2n+2))/2`.

Put

`c_n=sqrt((2n)!)/(2^n n!)=sqrt((1/2)_n/n!)`.

For every `n>=0` and real `t`,

`int p_n^infinity(s) exp(i t s)dmu_infinity(s)
 =i^n c_n phi(t)tanh(t)^n`.                                (6)

### Proof of (6)

Write the left side as `F_n(t)`. Differentiation under the integral and the Jacobi recurrence give

`F_n'(t)=i(a_(n-1)F_(n-1)(t)+a_nF_(n+1)(t))`.              (7)

The formula is true at `n=0`. Suppose it is true at `n-1,n`. Since

`phi'(t)=-(1/2)phi(t)tanh(t)`, `tanh'(t)=1-tanh(t)^2`,

differentiating the claimed expression for `F_n` gives

`F_n'(t)/i
 =i^(n-1)c_n phi(t)
   (n tanh(t)^(n-1)-(n+1/2)tanh(t)^(n+1))`.

The degree-`n-1` term cancels `a_(n-1)F_(n-1)` because

`n c_n=a_(n-1)c_(n-1)`.

The remaining term, divided by `a_n`, is the claimed expression for `F_(n+1)`, since

`c_(n+1)=c_n(n+1/2)/a_n`.

This proves (6) by induction. The differentiations are justified by the finite moments and exponential
decay of the Gamma density.

## Proof of the alternating semilocal tower

For `r_p=p^(-1/2)` and `ell_p=log p`, the product Poisson expansion is uniformly absolutely
convergent:

`G_P(s)=prod_(p in P)(1-r_p^2)^(-1)
 sum_(m in Z^P)(prod_(p in P)r_p^|m_p|)
 exp(i(sum_(p in P)m_p ell_p)s)`.                          (8)

It can be integrated termwise against every fixed polynomial times `dmu_infinity`. If `m!=0`, unique
factorization gives

`sum_(p in P)m_p log p!=0`.                                (9)

For `n=2k`, equation (6) becomes

`F_(2k)(t)=(-1)^k c_(2k)phi(t)tanh(t)^(2k)`.               (10)

The zero frequency in (8) contributes zero because `k>=1`. By (9), every other frequency is nonzero;
`c_(2k)>0`, `phi(t)>0`, and `tanh(t)^(2k)>0` there. Every Poisson coefficient is strictly positive.
Thus the unnormalized integral has the strict sign `(-1)^k`, and division by the positive normalizing
mass proves (1).

Since `N_Pp_0^P=0` and `N_infinity p_(2k)^infinity=2k p_(2k)^infinity`, self-adjointness of `N_P` on
the polynomial core gives

`<p_0^P,(N_PJ_P-J_PN_infinity)p_(2k)^infinity>_P
 =-2k int p_(2k)^infinity dnu_P`.

Equation (2) follows from (1), and (3) follows because the common multiplication term `-D^2`
intertwines the polynomial identity map.

Finally

`p_2^infinity(s)=(s^2-1/2)/sqrt(3/2)`.

The `k=1` sign is therefore equivalent to `int s^2dnu_P<1/2`. Positivity of the density and its full
support give the strict lower bound. The first Jacobi recurrence gives `a_0(P)^2=int s^2dnu_P`, proving
(4), while the last displayed defect identity gives (5). The Lean theorem
`semilocalArchimedeanSecondMomentCovarianceKernel_neg` checks the equivalent pointwise kernel identity

`-phi''(t)-phi(t)/2=-(3/4)phi(t)tanh(t)^2<0` for `t!=0`.

## Attack and limits

- `[PROVED]` The theorem survives cyclic-vector normalization and detects the normalized Jacobi
  grading rather than total spectral mass.
- `[PROVED]` It holds for every finite nonempty set of distinct primes and every positive even Jacobi
  degree, without a perturbative or small-prime-parameter hypothesis.
- `[PROVED]` The ground-state row of the formal prolate naturality defect has nonzero entries on every
  positive even archimedean mode, with alternating signs.
- `[PROVED]` No zero data, RH assumption, numerical experiment, prime exhaustion, or limiting cutoff
  enters the proof.
- `[OPEN CORE]` These are cyclic polynomial-core coefficients. The theorem does not show that any one
  of them survives the exact Sonin projection or a closed relative-resolvent realization.
- `[OPEN CORE]` Alternating nonzero entries are not positivity of the full Weil functional and do not
  imply RH.

## Novelty and significance audit

- **Proof gate:** complete above. The all-degree transform law is proved from the parent Jacobi
  recurrence, and unique factorization removes every nontrivial zero frequency.
- **Significance gate:** passed provisionally. A qualitative source remark that the number operators do
  not intertwine is sharpened to an infinite, normalized, explicitly signed tower for every finite
  prime set. The first-Jacobi contraction is only its lowest member.
- **Parent-theory gate:** the Gamma measure, archimedean Jacobi recurrence, metaplectic interpretation,
  and one-prime q-series are SEARCH. The claimed result is their all-finite-place assembly into (1)--(3).
- **Literature gate:** targeted searches of the two parent papers, their citations, and the semilocal
  Hermite/Jacobi literature found no all-even alternating Euler residue theorem.
- **Rediscovery gate:** the earlier unnormalized partition-mass cross-ratio was demoted to BRIDGE after
  cyclic normalization erased it. Every quantity here is measured in the normalized cyclic pair.

Scientific novelty remains provisional until independent experts verify the proof and literature
comparison.

## Formalization

The Lean development constructs the literal Gamma density and measure, proves all polynomial
moments and normalized mass, constructs the recurrence-selected Jacobi polynomials, and identifies
them as the unique degree-`n`, positive-leading-coefficient orthonormal family through
`semilocalArchimedeanJacobiGram_eq_ite`,
`semilocalArchimedeanJacobiPolynomial_natDegree`, and
`semilocalArchimedeanJacobiPolynomial_leadingCoeff_pos`.

The numbered claims are represented by the following checked declarations:

- `(1)` `semilocalFinitePrimeActualEvenJacobiMoment_signed_pos`;
- `(2)` `semilocalFinitePrimeActualGradingGroundDefect_signed_pos`;
- `(3)` `semilocalFinitePrimeActualProlateGroundDefect_signed_pos`;
- `(4)` `semilocalFinitePrimeNormalizedSecondMoment_bounds`;
- `(5)` `semilocalFinitePrimeActualGradingGroundDefect_one_eq_explicitResidue`;
- `(6)` `semilocalArchimedeanJacobiFourier_eq_closedForm`;
- `(7)` `hasDerivAt_semilocalArchimedeanJacobiFourier_succ_recurrence`;
- `(8)` `semilocalFinitePrimeEulerDensity_eq_poissonSeries_complex`, together with the termwise
  integration theorems in `SoninSemilocalFinitePrimeMeasure.lean`;
- `(9)` `semilocalNonzeroPrimeLogFrequency_ne_zero`;
- `(10)` `semilocalArchimedeanJacobiFourierClosedForm_even` and
  `semilocalArchimedeanEvenJacobiKernel_signed_pos`.

The grading and prolate operator notation is reduced to its exact ground-state scalar coefficient;
the common multiplication term is eliminated before definition, so the formal objects contain no
unproved operator-domain premise. The direct module checks, standard-axiom audit, and repository
formal lint gate pass without `sorry`, `admit`, project axioms, `opaque`, or `unsafe` declarations.

## Next move

Use the tower as a discriminator for any proposed closed semilocal prolate extension: its resolvent
comparison must reproduce these polynomial-core residues and derive a source-selected boundary
condition. Then determine whether resolvent smoothing sends the infinite ground-state row to a trace
class Sonin corner or erases it.
