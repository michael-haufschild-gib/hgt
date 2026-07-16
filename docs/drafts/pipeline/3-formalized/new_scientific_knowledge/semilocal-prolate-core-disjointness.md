# Semilocal cyclic--transported prolate core disjointness

- **ID:** semilocal-prolate-core-disjointness
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Scientific status:** CANDIDATE NEW SCIENTIFIC KNOWLEDGE, provisional pending independent review
- **Parent source:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2
- **Input:** `semilocal-grading-deformation-unbounded.md`

## Statement

Fix a prime `p`. In the canonical spectral realization of the one-prime semilocal cyclic pair, let

`E=C[s]`

be the polynomial cyclic core. Let

`w_p(s)=|1-p^(-1/2)exp(i log(p)s)|^2`

be the positive Euler metric. The exact Sonin transport `theta_p` sends the archimedean polynomial
core to

`E_theta=w_pE`.

Then

`E intersect E_theta={0}`.                                  (1)

Equivalently, after pullback through `theta_p`, the transported number-operator core is `E`, while
the semilocal cyclic core is

`G_pE`, `G_p=w_p^(-1)`,

and

`E intersect G_pE={0}`.                                    (2)

The domain mismatch persists at quadratic-form strength. For the archimedean ground state `p_0`,

`G_pp_0 in Dom((N_infinity+1)^alpha)` if and only if `alpha<1/4`. (3)

In particular

`G_pp_0 notin Dom((N_infinity+1)^(1/4))`

and hence is not in the transported number-form domain `Dom(N_infinity^(1/2))`.

Thus the genuine cyclic grading and the `theta_p`-transported grading have neither a common natural
algebraic core nor a common natural quadratic-form domain containing the cyclic ground state.

## Proof of algebraic core disjointness

In canonical spectral coordinates, the cyclic transition `eta_p` is the identity on functions and the
source relation is

`eta_p=theta_pG_p`.

Therefore `theta_p` is multiplication by `G_p^(-1)=w_p`, proving the description of `E_theta`.

Suppose `P,Q` are polynomials and

`P(s)=w_p(s)Q(s)`

almost everywhere on the real line. Both sides are restrictions of entire functions, so the identity
theorem makes the equality entire. If `Q!=0`, then `w_p=P/Q` is rational. But `w_p` is a nonconstant
entire periodic function of `s`. A rational periodic function is constant: a finite pole would produce
infinitely many translated poles, while a pole-free rational function is a polynomial and a periodic
polynomial is constant. Contradiction. Hence `Q=0` and then `P=0`, proving (1).

Multiplication by the nowhere-zero `G_p` carries (1) to (2).

## Proof of the quarter-derivative threshold

Let `p_n` be the archimedean Jacobi basis. Self-adjointness of `G_p` and the sharp coefficient estimate
from `semilocal-grading-deformation-unbounded.md` give

`|<p_(2k),G_pp_0>|=|<p_0,G_pp_(2k)>|asymp_p k^(-3/4)`,

while every odd coefficient vanishes. Therefore

`||(N_infinity+1)^alphaG_pp_0||^2`

is finite exactly when

`sum_(k>=1)(2k+1)^(2alpha)k^(-3/2)`

converges. This is equivalent to

`2alpha-3/2<-1`,

or `alpha<1/4`, proving (3).

## Route consequence

- `[PROVED]` The symbolic identity
  `W_p^cyc=W_p^theta+lambda^2(N_p-theta_pN_infinitytheta_p^(-1))` is not an operator identity on a
  common polynomial core; the two natural cores intersect only at zero.
- `[PROVED]` The cyclic ground state pulled into the transported control has less than one quarter of
  a Jacobi derivative. It is outside the transported number-form domain.
- `[CLOSED SHORTCUT]` Neither bounded perturbation theory nor a standard common-form KLMN argument can
  construct the genuine cyclic prolate operator from the transported control while retaining the
  natural cyclic core.
- `[OPEN CORE]` A successful comparison must construct a new graph domain or boundary relation not
  inherited from either natural core, and then prove that it still realizes the source cyclic grading
  and exact Sonin sector.
- `[OPEN CORE]` The theorem does not prove that the formal cyclic sum itself has no self-adjoint
  extension; it proves that the transported-control perturbation route cannot supply one on the
  source cores.

## Novelty and significance audit

- **Proof gate:** complete above.
- **Significance gate:** passed provisionally. The parent paper explicitly leaves the semilocal
  prolate domain formal. This theorem identifies a sharp source obstruction: the natural cyclic and
  Sonin-transported constructions do not even meet on a nonzero algebraic core, and their ground-state
  form domains are incompatible.
- **Parent-theory gate:** the two source maps and Euler metric are SEARCH. Core disjointness and the
  exact quarter-derivative threshold are the claimed new consequences.
- **Literature gate:** targeted searches found no statement of this core-disjointness or Jacobi
  regularity threshold in the semilocal prolate literature.

Scientific novelty remains provisional pending independent proof and literature review.

## Lean boundary

`formal/GaloisForLFunctions/RHTower/SoninSemilocalGradingBounds.lean` formalizes both theorem
components:

- `mellinCharacter_add_eulerPeriod` and `semilocalPrimeWeight_periodic` prove the exact Euler
  period of the spectral metric;
- `semilocalPrimeWeight_halfPeriod_ne_zero` proves that this periodic metric is nonconstant;
- `semilocalPrimeWeight_polynomial_core_disjoint_ae` proves
  `C[s] intersect w_p C[s]={0}` in the spectral almost-everywhere sense;
- `semilocalPrimeWeight_inv_polynomial_core_disjoint_ae` proves the inverse-metric form
  `C[s] intersect w_p^(-1) C[s]={0}`;
- `semilocalOnePrimeTransportedGroundDomainSquare` is the squared Jacobi-domain summand for
  `(N_infinity+1)^alpha G_p p_0`;
- `semilocalOnePrimeGroundDomainSquare_comparable` compares it, beyond the harmless zeroth
  coefficient, to the already-controlled semilocal commutator row;
- `summable_semilocalOnePrimeTransportedGroundDomainSquare_iff` proves summability exactly when
  `alpha < 1/4`.

The already-formalized semilocal transport square and Gram identity identify the same actual Euler
metric.  No proposition-valued analytic assumption is used.

## Gates

- [x] exact Sonin transport and Euler metric identified on paper
- [x] polynomial-core disjointness proved on paper
- [x] sharp Jacobi coefficient order proved in Lean
- [x] exact `alpha < 1/4` transported-ground-state threshold proved in Lean
- [x] actual periodic Euler-metric core disjointness formalized in Lean
- [ ] independent proof and literature review
