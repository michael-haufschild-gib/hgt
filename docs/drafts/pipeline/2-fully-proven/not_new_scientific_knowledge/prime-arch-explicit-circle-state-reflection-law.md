# Prime--archimedean explicit circle-state and reflection-polarization law

- **ID:** `prime-arch-explicit-circle-state-reflection-law`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE] [BRIDGE] [NOT AN RH PROOF]`
- **Parents:** `xi-radial-jensen-schur-capacity-rigidity`,
  `prime-arch-central-moment-germ`, `prime-arch-scaled-hausdorff-divisor-value-law`,
  `phase-radial-toeplitz-hankel-polarization-law`,
  `prime-arch-canonical-reflection-positive-equivalence`
- **Statement:** The normalized prime--Gamma reciprocal-moment functional has an unconditional,
  explicitly source-defined, uniformly coercive analytic probability density on the unit circle.
  Its ordinary unitary Gram form is positive with a quantitative gap.  RH is exactly the remaining
  Osterwalder--Schrader reflection positivity of that already constructed carrier, equivalently
  membership of its density in the closed convex hull of the radial Poisson kernels.  The density
  gap also proves an unconditional all-degree coefficient cone, leaving only tail-dominant
  polynomials in the RH test.

## Setup

For each multiplicity copy `q` of the Xi divisor put

```text
u_q = xiZeroCopyReciprocalSquare(q).
```

Let

```text
m_n = normalizedPrimeArchMoment(n) = sum_q u_q^(n+1),
M   = m_0 = primeArchCentralCurvature,
J   = sum_q |u_q|,
A   = sum_q |u_q|^2.
```

The formal corpus proves that every `m_n` is real, `M>0`, the displayed sums are absolutely
convergent, and

```text
|u_q| < R := 2/41,
(84/85) J <= M,
A <= R J.                                                    (1)
```

The second and third inequalities are the paper consequences of the formal height and
one-eighty-fourth orientation-sector laws used in
`xi-radial-jensen-schur-capacity-rigidity.md`.

Define the moment resolvent

```text
G_Xi(z) = sum_(n>=0) m_n z^n
        = sum_q u_q/(1-u_q z).                               (2)
```

It agrees near zero with the normalized continued prime--Gamma moment germ already formalized in
`PrimeArchCentralMomentGerm.lean`.

## 1. Explicit positive circle density

On the unit circle, with normalized Haar measure `dm`, define

```text
w_Xi(e^(it)) = M + 2 sum_(n>=1) m_n cos(nt)
             = 2 Re G_Xi(e^(it))-M.                          (3)
```

This series converges absolutely and real-analytically.  Indeed,

```text
|m_n| <= sum_q |u_q|^(n+1) <= R^n J,                       (4a)
```

so its Fourier coefficients decay geometrically, and

```text
sum_(n>=1) |m_n|
 <= sum_q sum_(n>=1) |u_q|^(n+1)
 =  sum_q |u_q|^2/(1-|u_q|)
 <= A/(1-R).                                                 (4)
```

Therefore

```text
M-2A/(1-R) <= w_Xi <= M+2A/(1-R).                            (5)
```

Using `(1)` and `R=2/41`,

```text
2A/((1-R)M)
 <= (4/39)(J/M)
 <= (4/39)(85/84)
 = 85/819.                                                   (6)
```

Consequently the exact source density is uniformly coercive:

```text
(734/819) M <= w_Xi(e^(it)) <= (904/819) M                  (7)
```

for every real `t`.  In particular

```text
d mu_Xi(e^(it)) = w_Xi(e^(it))/M dm(t)                       (8)
```

is an unconditional probability measure equivalent to Haar measure, with a positive
real-analytic density bounded above and below by explicit constants.

Fourier orthogonality gives, for every `k>=0`,

```text
integral_T zeta^k d mu_Xi(zeta) = m_k/M.                     (9)
```

Thus every normalized prime--Gamma moment is already an ordinary unitary moment of one explicit
source-defined positive carrier.  No Xi zero enumeration, RH assumption, weak limit, or abstract
representing-measure choice enters the definition `(3)`.

## 2. Explicit strict Schur source

The Caratheodory transform of `mu_Xi` is

```text
F_Xi(z) = 1 + (2/M) sum_(n>=1) m_n z^n
        = 2 G_Xi(z)/M-1.                                    (10)
```

Hence `Re F_Xi(z)>0` on the unit disk.  The associated Schur function is the exact source value

```text
phi_Xi(z) = (F_Xi(z)-1)/(F_Xi(z)+1)
          = 1-M/G_Xi(z).                                    (11)
```

It is not merely contractive.  From `(4)` and `(6)`, for `|z|<=1`,

```text
|G_Xi(z)-M|/M <= A/((1-R)M) <= 85/1638.
```

Therefore `G_Xi` has no zero on the closed unit disk and

```text
|phi_Xi(z)| <= 85/1553.                                     (12)
```

This closes the ordinary disk-state/Schur-carrier interface with a large strict margin.

## 3. Canonical unitary carrier and the reflected Hankel form

Let

```text
H_Xi = L^2(T,mu_Xi),
(U f)(zeta)=zeta f(zeta),
Omega=1,
(Theta f)(zeta)=f(conj(zeta)).                               (13)
```

Because `w_Xi` is real and even, `U` is unitary, `Theta` is a linear unitary involution,

```text
Theta U Theta = U^(-1),
<Omega,U^n Omega> = m_n/M.                                  (14)
```

More importantly, for all `i,j>=0`,

```text
<Theta U^i Omega,U^j Omega> = m_(i+j)/M.                    (15)
```

Thus the ordinary Gram kernel of the orbit is Toeplitz and unconditionally positive, while its
Theta-reflected Gram kernel is exactly the RH-bearing prime--Gamma Hankel matrix.  The carrier,
unitary action, reflection, cyclic vector, and ordinary metric are all unconditional; only the
orientation of the reflected form remains.

For a real polynomial

```text
P(z)=sum_(n=0)^N a_n z^n,
C_P(t)=a_0+sum_(n=1)^N a_n cos(nt),
S_P(t)=sum_(n=1)^N a_n sin(nt),                              (16)
```

evenness of `w_Xi` gives the exact polarization identity

```text
M^(-1) sum_(i,j) a_i a_j m_(i+j)
 = <Theta P(U)Omega,P(U)Omega>
 = ||C_P||^2_(L^2(mu_Xi))-||S_P||^2_(L^2(mu_Xi)).           (17)
```

Combining `(17)` with the formal integer-polynomial trace--Hankel criterion yields

```text
RH
 iff ||S_P||_(L^2(mu_Xi)) <= ||C_P||_(L^2(mu_Xi))
     for every P in Z[X].                                   (18)
```

The formal theta low-degree discharge sharpens the open test: it is enough to prove `(18)` for
the degree-at-least-two integer-polynomial tail.  Equivalently, after the first strict blocks are
discharged, one may prove positivity of the leading reflected Gram determinants from size three.

This is the top-down chain supplied by the theorem:

```text
source proof of weighted cosine--sine domination on the remaining tail cone
  + unconditional central-coefficient cone
  -> positivity of the explicit Theta-reflected unitary orbit
  -> prime--Gamma trace--Hankel positivity
  -> RH.                                                     (19)
```

The first line's tail-cone domination is the only open mathematical input in this formulation.

## 3a. Unconditional central-coefficient cone

The two-sided density estimate discharges a nontrivial all-degree part of `(18)`.  Write

```text
E_tail(P)=sum_(n=1)^N a_n^2.
```

Normalized Haar orthogonality gives

```text
||C_P||^2_(L^2(dm))=a_0^2+E_tail(P)/2,
||S_P||^2_(L^2(dm))=E_tail(P)/2.                            (17a)
```

Applying the lower density bound to the cosine term and the upper density bound to the sine term
in `(17)` yields

```text
M^(-1) sum_(i,j) a_i a_j m_(i+j)
 >= (734/819)*a_0^2-(85/819)*E_tail(P).                     (17b)
```

Consequently every real polynomial satisfying

```text
85*E_tail(P) <= 734*a_0^2                                  (17c)
```

has nonnegative prime--Gamma Hankel value unconditionally.  Combining `(17c)` with the formal
integer-polynomial criterion gives the strictly smaller terminal family

```text
RH
 iff the prime--Gamma Hankel value is nonnegative for every P in Z[X]
     satisfying 734*a_0^2 < 85*E_tail(P).                  (18a)
```

Thus any remaining counterexample must be quantitatively tail-dominant.  The reduction is
independent of degree and complements the theta discharge of degrees zero and one.

## 4. Exact radial Poisson-mixture chamber

For `0<=r<1`, let

```text
P_r(e^(it))=(1-r^2)/(1-2r cos(t)+r^2)
            =1+2 sum_(n>=1) r^n cos(nt)                     (20)
```

be the Poisson kernel.  Under RH every `u_q` is positive real.  Hence

```text
nu_Xi = M^(-1) sum_q u_q delta_(u_q)                         (21)
```

is a probability measure on `(0,2/41)`, and termwise use of `(20)` gives

```text
w_Xi/M = integral_[0,2/41] P_r d nu_Xi(r).                  (22)
```

Conversely, if the explicit source density `w_Xi/M` has any positive representation `(22)`, its
Fourier coefficients satisfy

```text
m_n/M = integral r^n d nu(r).
```

This is a positive representing measure for the complete normalized prime--Gamma moment
sequence, so the formal moment-measure capstone yields RH.  Therefore

```text
RH
 iff w_Xi/M belongs to the closed convex hull in C(T) of
     {P_r : 0<=r<=2/41}.                                    (23)
```

The topology in `(23)` may be taken to be the uniform norm.  Indeed, the map
`r |-> P_r` is continuous from the compact interval `[0,2/41]` into `C(T)`, so probability
mixtures form a compact convex set.  Equivalently, `(23)` is membership in the mass-one slice of
the closed positive cone generated by the same kernels.

Equation `(23)` separates the two positivity notions exactly:

```text
ordinary positive analytic circle density                  [unconditional]
radial positive Poisson mixture / reflected Hankel form     [equivalent to RH].
```

The missing theorem is not construction of a positive carrier.  It is radial disintegration of
the already explicit source carrier.

## 5. Coercivity cannot supply reflection positivity

There is no perturbative shortcut from `(7)` to `(18)`.  For every `0<epsilon<1` and every
positive integer `N`, the analytic even density

```text
w_(epsilon,N)(e^(it))=1-epsilon cos(2Nt)                    (24)
```

satisfies

```text
1-epsilon <= w_(epsilon,N) <= 1+epsilon,
```

so it can be arbitrarily close to Haar density and all of its ordinary Toeplitz sections are
strictly positive.  But for `P(z)=z^N`,

```text
integral_T P(zeta)^2 w_(epsilon,N)(zeta) dm(zeta)
  = -epsilon/2 < 0.                                         (25)
```

Thus no uniform `L^infinity` neighborhood of the Haar state lies inside the reflection-positive
cone.  The constant-density Hankel form is degenerate on every positive-degree monomial, so an
arbitrarily small Fourier perturbation can choose either orientation.  A proof of `(18)` must use
sign-structured source relations among the Fourier coefficients; the large margin `(7)` and the
strict Schur bound `(12)` cannot by themselves prove RH.

## 5a. Shifted descendant and valuation cones

The same circle construction applies after deleting finitely many source moments, but its central
mass must then be recovered from the atomwise sector rather than from `(1)`.  The descendant card
`prime-arch-shifted-sector-circle-valuation-cone.md` proves that for every `0 <= s <= 12`,

```text
w_(Xi,s)(e^(it))=m_s+2 sum_(n>=1)m_(s+n)cos(nt)
```

is a strictly positive real-analytic density.  If `P=X^v q`, the reflected Hankel value uses the
shift `s=2v`.  Consequently, for every `v<=5`,

```text
224*sum_(n>=1)b_n^2 <= (1960-13*(2v+1)^2)*b_0^2
  -> Q(X^v q)>=0.
```

This reaches nonconstant polynomials whose constant coefficient is zero, which the central cone
`(17c)` cannot see.  It also restricts the coupled-Sonin one-sided comparison to the complementary
residual family: comparison on that family plus these unconditional cones still gives the full
integer Hankel cone and RH.

The endpoint `s=12` is not obtained from the quadratic cosine bound.  The exact thirteenth-power
sector polynomial gives `Re(u^13)>|u|^13/8`, hence the additional valuation-six cone

```text
32*sum_(n>=1)b_n^2 <= 7*b_0^2 -> Q(X^6 q)>=0.
```

Its atomwise inequality, summed mass lower bound, and geometric tail envelope are formalized in
`PrimeArchShiftThirteenCircleCone.lean`.

## Attacks and verdicts

1. **Trace-norm attack.**  The circle state determines the analytic moments and therefore the
   full germ, but its ordinary norm is still `M`; it does not turn the radial mass `J` into a
   holomorphic norm.  The trace-norm gap from the parent card remains untouched.
2. **Toeplitz-to-Hankel attack.**  Reusing the same unitary orbit for both forms forces the
   two-periodic degeneracy formalized in `ToeplitzHankelPolarization.lean`.  The reflection
   `Theta` in `(15)` is essential.
3. **Small-Schur attack.**  The counterexample `(24)--(25)` proves that even an arbitrarily small
   Schur/Toeplitz perturbation can have the wrong reflected sign.  No norm-only argument survives.
4. **Wall-fraction attack.**  Wall's continued-fraction characterization converts `(23)` into
   scalar Hausdorff parameters, but those parameter inequalities are another exact form of the
   missing radial disintegration.  This is useful formal infrastructure, not an unconditional
   source proof.

The surviving contribution is therefore not a renamed RH equivalence.  It is the unconditional
construction and quantitative coercivity of the complete phase carrier, followed by the exact
identification of the one transverse orientation property that it does not contain.

## Literature calibration

The circle-state/Caratheodory construction and Wall's continued-fraction characterization are
classical; see A. D. Sokal,
[Wall's continued-fraction characterization of Hausdorff moment sequences](https://doi.org/10.1090/proc/14884).
The identification of reflected unitary representations with positive Hankel operators belongs to
the established reflection-positivity theory; see Adamo--Neeb--Schober,
[Reflection positivity and Hankel operators](https://arxiv.org/abs/2105.08522), and
Neeb--Olafsson,
[Reflection positivity for the circle group](https://arxiv.org/abs/1411.2439).
The project contribution is the explicit prime--Gamma density, its rational coercivity constants,
and the exact placement of the existing RH Hankel criterion inside that unconditional carrier.

## Formal reuse surface

The formal proof should reuse:

```text
summable_xiZeroCopyReciprocalSquare_pow
xiCentralReciprocalMoment_im_eq_zero
normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment
normalizedTraceMomentGerm_continuedPrimeArchSource_eventuallyEq_momentGerm
normalizedPrimeArchMoment_zero_pos
xiZeroCopy_fortyOne_div_two_lt_im_sq
xiThermalNode_pos
xiThermalOrientationTerm_le_one_over_eightyFour_node_sq
primeArchSourceTraceHankelIntNonnegative_iff_riemannHypothesis
primeArchSourceTraceHankelIntDegreeTwoTailNonnegative_iff_riemannHypothesis
primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis
```

`HTGeometry/BernsteinSzegoReconstruction.lean` already provides finite Toeplitz forms, while
`HTGeometry/ToeplitzHankelPolarization.lean` provides the phase--radial separation theorem.  The
missing reusable layer is an infinite absolutely summable Fourier-density wrapper and the
concrete `L^2` reflection carrier.

## Gates

- [x] 0 -> 1: source moment sequence and fixed unit-circle carrier identified
- [x] 1 -> 2: absolute Fourier convergence and explicit two-sided density bounds proved
- [x] 1 -> 2: exact strict Schur source and uniform bound proved
- [x] 1 -> 2: unitary/reflection polarization and weighted cosine--sine identity proved
- [x] 1 -> 2: all-degree central-coefficient positivity cone proved
- [x] shifted descendant: thirteen positive tail densities and seven valuation cones proved on
  paper; the new thirteenth-mass and tail estimates are formalized
- [x] 1 -> 2: radial Poisson-mixture equivalence proved from existing moment capstone
- [x] 1 -> 2: perturbative coercivity shortcut falsified by an exact positive-density family
- [ ] 2 -> 3: formalize the Fourier density, source carrier, and reflection identities
- [ ] proof input: prove radial Poisson disintegration, or equivalently weighted cosine--sine
  domination on the remaining degree-at-least-two tail-dominant coefficient cone, from the
  prime--Gamma source without importing divisor orientation or an RH-equivalent representing
  measure
