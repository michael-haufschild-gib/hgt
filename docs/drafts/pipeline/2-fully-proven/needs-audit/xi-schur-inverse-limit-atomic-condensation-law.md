# RH is the inverse limit of strict Xi Schur chambers with atomic carrier condensation

- **ID:** `xi-schur-inverse-limit-atomic-condensation-law`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** EXACT RH-EQUIVALENT BRIDGE / INVERSE-LIMIT CARRIER LAW
- **Lane:** application to RH after the general HT theorem
- **Scientific status:** `[PROVED HERE] [LIKELY BRIDGE] [NOVELTY UNVERIFIED]`
- **Parents:** `singular-maximal-ht-schur-defect-collapse-law.md`,
  `pick-defect-finite-selector-maximal-ht-phase-law.md`,
  `prime-arch-anti-herglotz-gate.md`
- **Statement:** A fixed normalized Schur germ constructed unconditionally from the centered Xi
  logarithmic derivative satisfies RH exactly when every one of its reduced finite
  Caratheodory--Fejer Pick matrices is positive definite, equivalently when every Schur defect is
  strictly positive. Under these conditions its completed circle carrier is infinite pure point,
  its Szego product is zero, and its canonical positive analytic Bernstein--Szego densities
  concentrate onto the Xi divisor with `L^p` norm tending to infinity for every `p>1`.

## Scope

This card applies a general carrier law to Xi only after that law has been proved for arbitrary
singular Herglotz carriers. It does not derive the required positivity from primes or Gamma data.
The equivalence below is therefore an exact route constraint, not a proof of RH.

## Fixed unconditional normalization

Let

```text
XiC(z)=xi(1/2+i z),
T_Xi(z)=XiC'(z)/XiC(z),
H_Xi(z)=-T_Xi(z),
chi(w)=i(1+w)/(1-w).                                      (1)
```

The point `z=i` corresponds to `s=-1/2`, so it is regular. Functional-equation symmetry gives

```text
b=-i H_Xi(i)=xi'(3/2)/xi(3/2).                            (2)
```

The standard positive theta integral for `xi` is strictly increasing on the real interval
`(1/2,infinity)`, hence

```text
b>0.                                                       (3)
```

Define the meromorphic disk germs

```text
F_Xi(w)=-i H_Xi(chi(w))/b,
f_Xi(w)=[F_Xi(w)-1]/[w(F_Xi(w)+1)].                        (4)
```

Equation `(2)` gives `F_Xi(0)=1`; therefore the second quotient in `(4)` is removable at zero.
All Taylor coefficients in `(4)` are defined unconditionally from the Xi germ.

For each `N`, let

```text
P_N^Xi = the reduced order-N Caratheodory--Fejer Pick matrix of f_Xi,
alpha_N^Xi = the N-th Schur parameter,
delta_N^Xi=1-|alpha_N^Xi|^2.                               (5)
```

Redundant jet functionals are deleted before `P_N^Xi` is formed.

## RH implies strict finite interior `[PROVED HERE]`

Assume RH. The even paired Hadamard product of `XiC` has only real zeros and gives, locally normally
in the upper half-plane,

```text
T_Xi(z)=sum_(gamma>0) m_gamma
  [1/(z-gamma)+1/(z+gamma)].                               (6)
```

Each summand has negative imaginary part. Thus `H_Xi=-T_Xi` is Herglotz on the full upper
half-plane. Equations `(1)--(4)` then make `F_Xi` a normalized Caratheodory function and `f_Xi` a
Schur function.

On the real boundary away from the Xi divisor, `H_Xi` is real, so `F_Xi` has zero real part there.
Consequently `f_Xi` is inner. The Herglotz measure of `F_Xi` is pure point on the Cayley images of
the real Xi zeros, with weights determined by their positive multiplicities and the fixed
normalization. The Xi divisor is infinite, hence this measure has infinite support and `f_Xi` is
not rational inner.

Every `P_N^Xi` is positive semidefinite because `f_Xi` realizes its data. It cannot be singular:
the singular Caratheodory--Fejer problem has a unique rational-inner solution, which would force
the actual germ and then the global Schur function to be rational inner. Therefore

```text
RH implies P_N^Xi>0 and delta_N^Xi>0 for every N.          (7)
```

## Cofinal strict positivity implies RH `[PROVED HERE]`

Assume every `P_N^Xi` is positive definite. In particular, the entire coefficient sequence in
`(4)` satisfies all finite Schur contractivity conditions. The Schur coefficient theorem produces
a Schur function `f` on the whole disk with exactly that Taylor series.

Reconstruct

```text
F(w)=[1+w f(w)]/[1-w f(w)],
H(z)=i b F(chi^(-1)(z)).                                   (8)
```

Then `F` is Caratheodory and `H` is Herglotz on the upper half-plane. Near `z=i`, equations
`(4)` and `(8)` give `H=H_Xi`. The meromorphic identity theorem extends this equality throughout
the upper half-plane. Since `H` is holomorphic there, every apparent upper-half-plane pole of
`H_Xi` is removable; equivalently, `XiC` has no nonreal upper-half-plane zero.

On the centered upper half-strip this gives the anti-Herglotz inequality for the continued
prime--archimedean source. The formal theorem
`continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis` then yields RH.

The standard Schur recursion identifies positive definiteness of all leading reduced Pick matrices
with strict positivity of all successive defects. Combining both directions proves

```text
RH
 iff P_N^Xi is positive definite for every finite N
 iff delta_N^Xi>0 for every finite N.                      (9)
```

No finite matrix is singular on the RH side. The arithmetic carrier lies in the interior of every
finite Schur chamber; orientation is the completed inverse-limit condition.

## Atomic condensation forced by RH `[PROVED HERE VIA GENERAL LAW]`

Under the equivalent conditions `(9)`, the representing circle measure `mu_Xi` is pure point with
infinite support. Its Schur parameters therefore satisfy

```text
delta_N^Xi>0 for every N,
product_(N=0)^infinity delta_N^Xi=0.                       (10)
```

Let `G_N^Xi` be the Toeplitz Gram matrix of `1,z,...,z^N` for `mu_Xi`. It is positive definite at
every finite level, but `(10)` and the Toeplitz determinant factorization give

```text
lambda_min(G_N^Xi)->0,
condition_number(G_N^Xi)->infinity.                        (10a)
```

Indeed, the determinant geometric mean tends to zero, while `trace(G_N^Xi)=N+1` forces the largest
eigenvalue to be at least one. Thus RH requires strict finite positivity without a uniform
coercivity gap.

Let `phi_N` be its degree-`N` orthonormal polynomial and define the Bernstein--Szego measure

```text
d mu_Xi^[N](theta)=d theta/[2 pi |phi_N(e^(i theta))|^2]
                  =rho_N(theta)d theta/(2 pi).             (11)
```

Every finite measure `(11)` has positive real-analytic density, its transform is rational and
differentially algebraic, and it matches the first `N` Schur/Taylor coordinates of the Xi carrier.
Its Gram matrix through degree `N` is exactly `G_N^Xi`, so the canonical rational model already
reproduces the level-`N` loss of coercivity.
Nevertheless

```text
mu_Xi^[N] -> mu_Xi weakly,
F_Xi^[N] -> F_Xi locally uniformly.                        (12)
```

Let `E_Xi` be the Cayley image of the Xi divisor, enlarged by the possible point at infinity. It
is a Lebesgue-null carrier of `mu_Xi`. For every `epsilon>0`, choose an open neighborhood
`U_epsilon` of `E_Xi` with normalized Lebesgue measure below `epsilon`. Portmanteau gives

```text
lim_N integral_(U_epsilon) rho_N d theta/(2 pi)=1.         (13)
```

For every `p>1`,

```text
||rho_N||_(L^p) -> infinity.                               (14)
```

Otherwise a bounded infinite subsequence would have a weakly convergent `L^p` subsequence, and
its measure limit would be absolutely continuous. This contradicts the unique pure-point weak
limit `(12)`.

## Positive constraint on RH routes

Equations `(9)` and `(13)--(14)` give the route law:

> **A source-faithful Schur proof of RH must keep the Xi carrier strictly inside every finite Pick
> chamber while forcing its canonical positive analytic densities to condense onto an infinite
> atomic boundary only cofinally; strict positivity must persist while every uniform coercivity
> gap collapses.**

Thus finite singular interpolation is not the mechanism. Nor can a proof impose a uniform
`L^p`, `p>1`, bound on the canonical densities: such a bound would exclude the carrier required by
RH. Likewise, a uniform lower spectral bound for the canonical Toeplitz Gram sections is
incompatible with `(10a)`. The missing source theorem must control the whole nested family while allowing
precisely this loss of uniform integrability and coercivity.

If a proposed finite-prime source form `Q_N>=cI` is connected to `G_N^Xi` by a congruence
`G_N^Xi=W_N^*Q_NW_N`, the general metric-weld law forces

```text
sigma_min(W_N)->0.                                        (15)
```

Thus a unitary or uniformly invertible prime-to-Schur identification cannot be the missing
mechanism. The formalized `1/log N` prime-clock crossover provides a uniformly coercive normalized
source coordinate, but no zero-preserving theorem currently identifies it with the collapsing
Schur direction. Any successful identification must include the cofinal pinching `(15)` rather
than suppress it.

The graph-saturation companion sharpens `(15)`. Under RH, `mu_Xi` is purely singular, so the raw
analytic-polynomial identification has

```text
closure(Graph(A_(mu_Xi)))=H^2(m) times L^2(mu_Xi).        (16)
```

Its unique compatible positive-triangular repair is the Xi inverse-Cholesky/orthogonal-polynomial
tower `C_N`, with

```text
||C_N||=lambda_min(G_N^Xi)^(-1/2)->infinity.              (17)
```

Therefore an ordinary graph limit loses the entire Xi incidence relation. In the canonical
triangular category, a source proof must construct the divergent OPUC frame itself, or an
equivalent marked rigging, before taking the cofinal closure.

## Parent-theory and novelty attack

1. `[SEARCH]` Schur coefficient positivity, singular Pick uniqueness, Verblunsky recursion,
   Bernstein--Szego approximation, and Szego's product theorem are classical.
2. `[FORMALIZED INPUT]` The repository proves the full source anti-Herglotz/RH equivalence and the
   infinitude of the Xi divisor.
3. `[PROVED HERE]` The fixed normalization `(1)--(4)` makes the Xi Pick matrices, Verblunsky
   parameters, Herglotz measure, and zero divisor parts of one object.
4. `[PROVED HERE]` This yields the exact strict inverse-limit criterion `(9)` and the atomic
   condensation law `(13)--(14)`.
5. `[COMPANION CONSEQUENCE]` The general graph-saturation theorem gives `(16)--(17)` under RH.
6. Preliminary exact searches found no published Xi criterion in these Schur/Verblunsky
   coordinates. Nevertheless `(9)` is structurally a classical positivity reparameterization of
   RH, so it is classified as a likely bridge unless a priority audit shows otherwise.

## Honest significance score

**74/100 candidate; plausible range 62--84.** The formulation is exact and the carrier geometry is
useful, but the RH equivalence is a Schur-coordinate recoding of Herglotz orientation. The genuinely
new candidate remains the general residual singular-HT/transverse-skeleton theorem in the parent
card, not this application.

## Lean status

No Stage 3 claim is made. The source anti-Herglotz/RH equivalence is formalized, but the exact
normalization `(1)--(5)`, Schur coefficient theorem, OPUC carrier, Bernstein--Szego approximation,
and condensation theorem are not jointly formalized in Lean.

Formalization audit (needs-audit pass): the cited RH input is confirmed present and is the RH-facing
anchor — `RHTower.continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis` in
`CCMCompletedPrimeGammaAccretivityCriterion.lean`. But the inverse-limit criterion `(9)` and the
atomic-condensation law `(13)`--`(14)` need the Schur coefficient theorem, OPUC carrier, and
Bernstein--Szego `L^p` blow-up, all absent from mathlib. No bounded self-contained kernel closes a
gate; no partial file is added.

## Gates

- [x] unconditional Xi disk germ fixed
- [x] basepoint normalization and positivity of `b`
- [x] RH-to-nonrational-inner direction proved
- [x] all-finite-Pick-positivity-to-RH direction proved
- [x] strict Schur-defect equivalence proved
- [x] pure-point carrier and zero Szego product proved under RH
- [x] strict-but-noncoercive Toeplitz/Gram law proved
- [x] uniformly coercive source weld forced to pinch cofinally
- [x] raw Xi graph saturation and divergent triangular repair derived conditionally
- [x] Bernstein--Szego atomic condensation and all-`L^p` blow-up proved
- [x] route consequence stated positively
- [ ] independent specialist proof audit
- [ ] full priority audit
- [ ] unconditional Lean formalization of the entire theorem

## Log

- 2026-07-12 -- Separated the Xi application from the general HT carrier theorem. Fixed the
  unconditional normalization at `z=i`, proved the strict finite Pick/Schur inverse-limit
  equivalence to RH, and derived atomic condensation of the canonical Bernstein--Szego densities.
