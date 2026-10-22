# Deninger--Meyer secondary Poisson regulator

- **ID:** `deninger-meyer-secondary-poisson-regulator`
- **Stage:** 3-formalized
- **Type:** SECONDARY BOUNDARY REGULATOR AND EXACT BESSEL GRAPH DOMAIN
- **Label:** `DAC_DENINGER_MEYER_SECONDARY_POISSON_REGULATOR`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** Meyer--Poisson reflection supplies the unique scalar correction to raw prime sampling
  on a two-collar value space.  After polarized first-suspension transgression, this gives a
  quotient-corrected all-prime regulator whose maximal Bessel graph domain contains every literal
  Meyer boundary, whose Schwartz sector is continuous, and whose Green radical is exactly the
  reflected prime graph.

## 1. Problem solved

The source-derived raw restriction
\[
 {\cal R}_a(f)_p=p^{-1/2}f(p)T_p(a_p)
\]
is Bessel on radial Schwartz cochains, but the explicit boundary probe in the predecessor card
proved
\[
 (Zb)(p)\ne0
\]
for every prime.  Thus raw evaluation is not a map on
\(H_-/\operatorname{range}Z\).  The forced correction had to satisfy
\[
 {\cal H}_p(Zf)=(Zf)(p)                                      \tag{1}
\]
without factoring through the primary residue differential.

The construction below supplies `(1)` from the opposite Fourier collar.  It is not a scalar
chosen after seeing the target norm.

## 2. Meyer reflection as a concrete Calderón graph

For \(f\in H_\cap\), evenness and the two endpoint conditions give
\[
 f(0)=\widehat f(0)=0.
\]
Scaled Poisson summation gives
\[
 \sum_{n\in\mathbb Z}f(nx)
   =x^{-1}\sum_{n\in\mathbb Z}\widehat f(n/x),\qquad x>0.
\]
Removing the zero terms and identifying the positive and negative halves by evenness yields
\[
 \boxed{\;
   Zf(x)=x^{-1}Z\widehat f(x^{-1}).
 \;}                                                          \tag{2}
\]

The bilateral scaled Poisson theorem already existed in the repository.  Formula `(2)` is its
one-sided Meyer endpoint extraction; the classical Poisson identity itself is not claimed as new.

Define the two-collar trace and its conormal defect by
\[
 \operatorname{Tr}_x(f)
   =\bigl(Zf(x),Z\widehat f(x^{-1})\bigr),
\qquad
 \delta_x(u,v)=u-x^{-1}v.                                     \tag{3}
\]
Then `(2)` gives
\[
 \operatorname{Tr}_x(H_\cap)\subseteq
 \Gamma_x:=\ker\delta_x
   =\{(u,v):u=x^{-1}v\}.                                      \tag{4}
\]
The map \(\delta_x\) is surjective, since \(\delta_x(z,0)=z\).  Therefore
\[
 (\mathbb C^2/\Gamma_x)\cong\mathbb C                       \tag{5}
\]
canonically through \(\delta_x\).  This is the exact local boundary classification: no additional
scalar relation survives in the two-collar value space.

## 3. Quotient-corrected first-suspension regulator

For a packet coefficient \(a_p\in L^2(B_p)\), define
\[
 Q_{p,a_p}(u,v)
  =p^{-1/2}\delta_p(u,v)\,T_p(a_p).                            \tag{6}
\]
If \(a_p\ne0\), half-density is nonzero and \(T_p\) is injective.  Hence
\[
 \ker Q_{p,a_p}=\Gamma_p.                                     \tag{7}
\]
Thus `(6)` induces an injective map
\[
 \overline Q_{p,a_p}:\mathbb C^2/\Gamma_p
   \hookrightarrow
   L^2\!\left(B_p\times\mathbb R/\log p\,\mathbb Z\right).     \tag{8}
\]
Equations `(4)` and `(7)` show that every literal Meyer boundary maps to zero, while every
nonzero transverse quotient class is detected by every nonzero packet.

Raw evaluation is now correctly interpreted: it is the first leg \(u\) of `(3)`.  Its correction
is the reflected Fourier leg \(p^{-1}v\), which equals raw evaluation precisely on boundaries.

## 4. Maximal all-prime graph domain

For an algebraic radial cochain pair \(h=(h_+,h_-)\), put
\[
 {\cal Q}_a(h)_p
  =p^{-1/2}
    \left(h_+(p)-p^{-1}h_-(p^{-1})\right)T_p(a_p).              \tag{9}
\]
Define the maximal source graph domain
\[
 {\cal D}_a
  =\left\{h:
      \bigl({\cal Q}_a(h)_p\bigr)_p
      \in\bigoplus_p^{\ell^2}L^2(B_p\times S^1_{\log p})
    \right\}.                                                  \tag{10}
\]
Linearity of `(9)` and stability of `Memℓp` under addition and scalar multiplication make
\({\cal D}_a\) a complex submodule.  No auxiliary weight occurs in `(10)`; membership is defined
by the actual secondary values.

For \(f\in H_\cap\), the literal Poisson boundary pair
\[
 d f=(Zf,Z\widehat f)
\]
satisfies \({\cal Q}_a(df)_p=0\) for every prime by `(2)`.  Consequently
\[
 d(H_\cap)\subseteq{\cal D}_a,\qquad
 {\cal Q}_a\!\restriction_{d(H_\cap)}=0.                       \tag{11}
\]
This is stronger than formal quotient language: every boundary is admitted to the global Bessel
domain before being killed.

The exact maximal-domain kernel is
\[
 {\cal Q}_a(h)=0
 \iff
 \forall p,\quad
 h_+(p)=p^{-1}h_-(p^{-1})
 \ \text{or}\ a_p=0.                                          \tag{12}
\]

## 5. Continuous Schwartz sector

Assume \(\|a_p\|\le B\).  For a pair of Schwartz collars \((f,g)\), formula `(9)` becomes
\[
 {\cal Q}_a(f,g)_p
 =p^{-1/2}\left(f(p)-p^{-1}g(p^{-1})\right)T_p(a_p).            \tag{13}
\]
The physical leg obeys the predecessor estimate
\[
 \|p^{-1/2}f(p)T_p(a_p)\|
 \le Bq_{1,0}(f)p^{-3/2}.
\]
The reflected leg has the independent bound
\[
 \|p^{-3/2}g(p^{-1})T_p(a_p)\|
 \le Bq_{0,0}(g)p^{-3/2}.                                     \tag{14}
\]
Both square sums are dominated by \(\sum_pp^{-3}\).  Hence `(13)` defines a continuous
complex-linear map
\[
 {\cal S}(\mathbb R)^2
   \longrightarrow
 \bigoplus_p^{\ell^2}L^2(B_p\times S^1_{\log p}),              \tag{15}
\]
and its image agrees with the restriction from the maximal domain `(10)`.

The pulled-back full-block Green energy is nonnegative and has exact radical
\[
 G_a^{\rm sec}(f,g)=0
 \iff
 \forall p,\quad
 f(p)=p^{-1}g(p^{-1})
 \ \text{or}\ a_p=0.                                          \tag{16}
\]

## 6. Actual rational-Witt nonvacuity

Take a nonzero finite packet function at one prime, its actual
arithmetic-Frobenius-fixed rational-Witt witness, and extend the packet by zero at the other
primes.  For any Schwartz \(f\) with \(f(p)\ne0\), the pair \((f,0)\) lies off the reflected graph
at \(p\).  Its secondary energy is exactly the predecessor raw energy and is strictly positive.

Thus the boundary correction does not collapse the finite Wrat channel.  It kills precisely the
source relation `(2)`, not every rational-Witt packet.

## 7. Hostile audit

- **Classical part identified.**  Scaled Poisson summation is existing mathematics and existing
  repository infrastructure.  New result is its Meyer endpoint extraction and assembly with
  reflected collars, polarized first modes, maximal all-prime graph domain, and Wrat Green
  radical.
- **Not target-weight theatre.**  The only coefficients are source-forced \(p^{-1/2}\), Poisson
  reflection \(p^{-1}\), and first suspension transgression.  Domain `(10)` is defined by the
  resulting vector itself.
- **Not an abstract quotient with no boundary inclusion.**  The literal pair
  \((Zf,Z\widehat f)\) is constructed as an element of `(10)` and maps pointwise and globally to
  zero.
- **Not residue factorization.**  The correction uses the opposite Fourier collar.  It does not
  factor through the codimension-one residue differential killed by the prior no-go.
- **Not scalar packet collapse.**  The whole Haar-\(L^2(B_p)\) coefficient survives through
  \(T_p\).
- **Not full Route L closure.**  The missing theorem is identification of this separated
  two-collar graph complex with the literal sheafified arithmetic relevant complex, plus proof
  that no further closed middle-boundary relations arise there.  Cup/trace/Hodge/Xi gates remain.

## 8. Novelty audit

Primary-source audit:

- Meyer constructs a nuclear Fréchet spectral quotient and the zeta-zero action;
- Deninger constructs rational-Witt arithmetic dynamical spaces and explains the missing
  cohomological program;
- Paugam constructs the spectral symplectic pairing;
- Deninger's later rational-Witt sheaf paper studies sheafification and finite relative
  correspondences.

No located primary source states `(6)`--`(16)`: the inverse-collar Calderón quotient, its
polarized rational-Witt first-mode injection, the maximal all-prime Bessel domain containing every
Meyer boundary, the continuous two-Schwartz-collar restriction, or its exact Green radical.
Repository search found the bilateral Poisson identity and each local ingredient separately, but
not this secondary assembly.  External priority remains provisional pending specialist review.

## 9. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/Deninger/DeningerMeyerPoissonCalderonGraph.lean`;
- `GaloisForLFunctions/RHTower/Deninger/DeningerMeyerSecondaryPoissonRegulator.lean`.

Capstones:

1. `deningerMeyerPoisson_reflection`;
2. `deningerMeyerPoissonCalderonQuotientEquiv`;
3. `deningerMeyerPoissonCalderonPacketRegulator_injective`;
4. `deningerMeyerPoissonBoundaryInSecondaryBesselDomain`;
5. `deningerMeyerPoissonBoundary_secondaryRestriction_zero`;
6. `deningerMeyerSecondarySchwartzRestrictionCLM`;
7. `deningerMeyerSecondarySchwartzGreenEnergy_eq_zero_iff`;
8. `deningerFiniteRationalWittSecondarySchwartz_pos_globalGreenEnergy`.

No `sorry`, `axiom`, `opaque`, `unsafe`, numerical computation, Xi divisor, zeta zero, or
RH-equivalent hypothesis is used.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Frédéric Paugam, *Spectral symmetries of zeta functions*,
  https://arxiv.org/abs/0803.0199.
- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  https://arxiv.org/abs/2508.05329.

## Log

- 2026-08-02 — Raw-boundary obstruction converted into the reflected Fourier-collar conjecture.
- 2026-08-02 — Meyer reflection extracted from the existing bilateral scaled Poisson theorem;
  exact Calderón graph quotient and packet injection proved.
- 2026-08-02 — Maximal all-prime secondary Bessel domain constructed; literal Meyer boundaries
  proved admitted and killed.
- 2026-08-02 — Continuous Schwartz-pair restriction, exact Green radical, and finite Wrat positive
  admission proved and Lean-formalized.
