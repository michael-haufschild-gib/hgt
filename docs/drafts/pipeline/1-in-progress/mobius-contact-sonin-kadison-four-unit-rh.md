# Möbius-contact Sonin--Kadison realization of the four-unit Xi boundary budget

- **ID:** `mobius-contact-sonin-kadison-four-unit-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HTGEOMETRY-TO-RHTOWER TRANSFER / RH ROUTE
- **Scientific status:** `[CONJECTURE] [DOWNSTREAM IMPLICATION PROVED] [FINITE ENERGY ALGEBRA
  PROVED ON PAPER; COMPONENTS FORMALIZED] [SOURCE INCIDENCE OPEN] [NOVELTY UNVERIFIED]`
- **HT parents:**
  - `../3-formalized/finite-clock-star-kadison-observability.md`
  - `calibrated-clock-curvature-class.md`
  - `constraint-curvature-integration-stack.md`
- **RH parents:**
  - `../3-formalized/infinite-mobius-critical-boundary-layer-product.md`
  - `../3-formalized/not_new_scientific_knowledge/mobius-critical-fisher-stein-contact-law.md`
  - `../3-formalized/luders-pinching-sonin-commutator-discharge.md`
  - `../2-fully-proven/not_new_scientific_knowledge/ccm-hankel-boundary-relative-trace-four-unit-law.md`
  - `../2-fully-proven/not_new_scientific_knowledge/ccm-boundary-strip-weak-compactness-transfer-law.md`
- **Statement:** Realize the completed all-prime contact-to-Xi continuation as the boundary
  disturbance of a source-calibrated Sonin/Lueders clock.  The exact Kadison energy partition then
  transports the incoming four-unit budget without an additional inequality and proves RH.

## Goal

Replace the still-open finite-stage estimate

```text
||A_(N,u)||_HS^2 <= 4(1-exp(-u))+o(u)                    (1)
```

by a source construction which makes `(1)` a projection-energy identity.  The construction must
start from the positive squarefree-Mobius boundary layer, its signed all-prime response, the
archimedean completion, and the Sonin cutoffs.  It may not start from `Xi` residues or from an
arbitrary contraction between two vectors.

## Exact proved endpoints

The source side is already fixed before any divisor is read:

```text
rho(y)=exp(-y) 1_(y>0),
s(y)=1-y,
integral |2s(y)|^2 rho(y)dy=4,                            (2)
```

and the formal all-prime moving-aperture response satisfies the exact positive/signed contact
limit recorded in `mobius-critical-fisher-stein-contact-law.md`.

The target side has the closed anti-causal Xi operator `D_Xi`.  If `Q_u` is the output cutoff onto
`[0,u)`, its extended boundary energy is

```text
Delta_Xi(u)=||Q_u D_Xi||_(HS,ext)^2.                     (3)
```

The parent four-unit theorem proves

```text
limsup_(u->0+) Delta_Xi(u)/(4(1-exp(-u))) <= 1
  -> RH.                                                  (4)
```

## Source-clock conjecture

`[CONJECTURE]` There are finite-stage Hilbert--Schmidt source observables `X_(N,u)`, source-selected
Sonin clock projections `P_(N,u)`, and Lueders channels

```text
Phi_(N,u)(X)=P_(N,u) X P_(N,u)
  +(1-P_(N,u)) X (1-P_(N,u))                             (5)
```

with the following properties.

1. **Contact calibration.**  The total source energy is the incoming boundary budget:

   ```text
   limsup_N ||X_(N,u)||_HS^2 <= 4(1-exp(-u))+o(u).        (6)
   ```

   The normalization in `(6)` is fixed by the completed Mobius score `(2)`, not fitted to the
   target.

2. **Boundary disturbance.**  Put

   ```text
   A_(N,u)=X_(N,u)-Phi_(N,u)(X_(N,u)).                   (7)
   ```

   The exact Lueders/Kadison orthogonal decomposition gives

   ```text
   ||A_(N,u)||_HS^2 <= ||X_(N,u)||_HS^2.                 (8)
   ```

3. **Graph-core incidence.**  On one source-defined graph core `C_Xi`,

   ```text
   A_(N,u) f -> Q_u D_Xi f weakly                        (9)
   ```

   for every `f in C_Xi`.

The weak Hilbert--Schmidt transfer theorem applies to `(8)`--`(9)`, gives `(4)`, and proves RH.

## Why the energy estimate is no longer independent

For an orthogonal projective measurement, Lueders pinching is the `Z_2` clock twirl and the
disturbance is the erased operator component.  `SoninLudersPinching.lean` proves that its
Hilbert--Schmidt energy is exactly the cutoff-commutator energy.  The new arbitrary-operator
star-Kadison law proves the corresponding erased-vector identity without self-adjointness, and
the polarized scratch theorem proves all two-observable cross terms.

Therefore `(8)` is not an analytic estimate to be proved after constructing `A_(N,u)`.  It is
forced by the clock realization `(7)`.  Relative to the existing boundary-strip transfer theorem,
this moves the positive-budget obligation to the source norm calibration `(6)`.  It is a genuine
gain only if `(6)` follows directly from the Möbius contact observable rather than being fitted to
the boundary strip.  The remaining obligations are contact calibration and source incidence `(9)`.

## Smallest non-circular construction

The first acceptable brick is one finite prime-power packet and the completed archimedean contact
channel on the doubled causal/anti-causal graph.  It must prove directly that:

```text
completed contact operator
  - its Sonin Lueders pinching
= the finite boundary strip of the signed prime--Gamma logarithmic graph.   (10)
```

The prime-power packet must remain channel-resolved.  At a single prime-power `n`, the diagonal
contribution of the paired Xi kernel changes sign with the phase `Im(w) log(n)`, so no orthogonal
prime-by-prime positive Gram can satisfy `(10)`.  The time-one Gamma covariance and the
archimedean boundary term must be present before the positive square is formed.

## Attacks

1. **Arbitrary contraction redressing.**  Postulating a contraction sending the pole vector to
   the Xi residue vector is exactly the four-unit RH criterion.  The maps in `(5)`--`(10)` must be
   written from source generators.
2. **Finite-prime continuation.**  Every finite-prime logarithmic source has only the incoming
   Euler pole in the anti-causal half-plane.  Locally uniform Euler-side convergence does not imply
   `(9)`; the all-prime contour jump is the load-bearing topology.
3. **Infinitesimal Gamma roots.**  Splitting the time-one completion into independently passive
   convolution-root clocks fails even for the actual Xi two-node kernel.  The source clock must be
   a coupled time-one operation.
4. **Bare curvature.**  A calibrated clock-curvature field supplies the candidate finite shadows
   and their integration problem, but self-duality does not orient the boundary energy.  The
   concrete Hilbert realization `(5)` and the equality `(10)` are mandatory.
5. **Prime algebraic independence.**  The new prime-power differential-matroid theorems prevent
   finite coefficient fields from hiding active prime directions.  They certify source labels;
   they do not imply the Hilbert inequality or the graph-core convergence.
6. **Off-diagonal dilation tautology.**  Every Hilbert--Schmidt operator can be installed as the
   erased block of a two-sector pinching after enlarging the Hilbert space.  Thus the existence of
   `(5)`--`(8)` alone is equivalent to relabelling `A_(N,u)`.  The direct completed-source identity
   `(10)` and the independently normalized contact bound `(6)` carry all non-circular content.

## Native commutator formulation

The source observable and the target ideal are now fixed more tightly than `(5)`--`(10)`.  Let
`psi_sigma` and `chi_sigma` be the normalized squarefree-Möbius state and completed Fisher tangent.
The source contact observable is

```text
X_sigma=2^(-1/2)(|chi_sigma><psi_sigma|
                   +|psi_sigma><chi_sigma|)
       =2sqrt(2)(sigma-1) partial_sigma
          |psi_sigma><psi_sigma|.                       (11)
```

Thus `X_sigma` is the normalized derivative of the pointed source projection, and
`||X_sigma||_HS^2->4`.  It is not an operator to be selected during the Sonin construction.

For the scaled divisor cutoff `P_(sigma,u)`, the exact theorem in
`../2-fully-proven/mobius-fisher-contact-commutator-ward-budget.md` gives

```text
lim_(sigma->1+) ||[P_(sigma,u),X_sigma]||_HS^2
 =E_W(u)
 =4[(2+u^2)e^(-u)-2(1+2u^2)e^(-2u)],                  (12)

E_W(u)<=8(1-e^(-u)),
lim_(u->0+)E_W(u)/(2u)=4.                               (13)
```

The factor eight is forced by the two adjoint cutoff orientations.  This matches the already
proved RH consumer

```text
limsup_(u->0+) 1/(2u)||[P_u,D_Xi]||_(HS,ext)^2<=4
  -> RH.                                                  (14)
```

Accordingly the proof-bearing source identity is not a two-sided Lüders disturbance converging to
the one-sided strip `Q_uD_Xi`.  It is a completed source commutator

```text
completed image of [P_(sigma,u),X_sigma]
  -> [P_u,D_Xi]                                          (15)
```

on one source-defined graph core, with no increase of Hilbert--Schmidt energy.  Lüders pinching
remains useful because its disturbance has exactly the commutator energy, but `(15)` preserves its
native two-sided geometry and the exact factor two.

This also fixes the finite observable in the smallest brick.  The finite prime-power/Gamma/Sonin
construction must act on `(11)` and intertwine its source cutoff with the physical boundary
cutoff.  Producing an arbitrary `X_(N,u)` of the right norm is no longer admissible.

## Lean boundary

The following algebraic and finite-Hilbert pieces are already formalized:

- exact Mobius critical contact and its four-unit incoming energy;
- Lueders pinching as a `Z_2` twirl;
- disturbance/commutator equality and Hilbert--Schmidt energy equality;
- Sonin projection and finite time--frequency area laws;
- arbitrary-operator finite-clock star-Kadison energy.

The two-observable star-Kadison covariance was additionally verified in
`/tmp/FiniteClockStarKadisonCovariance.lean`, with only the standard Lean axioms.  No Lean wrapper
from `(9)` to RH should be added: the analytic graph-core incidence and boundary limit, not the
finite algebra, are the proof-bearing theorem.

## Gates

- [x] 0 -> 1: source-pure construction target and exact RH consumer isolated
- [x] incoming four-unit contact energy formalized
- [x] finite Lueders/Kadison disturbance identities formalized; total contraction proved on paper
- [x] source contact observable fixed as the pointed Fisher-connection derivative
- [x] exact local commutator profile and native eight-to-four normalization proved on paper
- [x] boundary-strip weak-limit transfer theorem available on paper
- [ ] construct the finite prime-power/Gamma/Sonin image of `(11)`
- [ ] prove the direct source commutator identity `(15)`
- [ ] prove graph-core convergence to `[P_u,D_Xi]`
- [ ] prove nonexpansiveness in the completed Hilbert--Schmidt metric
- [ ] deduce `(14)` and RH
- [ ] parent-theory and scientific-novelty audit

## Log

- 2026-07-15 -- Opened after the star-Kadison/constraint-curvature audit showed that the positive
  finite-stage budget can be made structural; the remaining theorem is the source-pure
  contact-to-Xi graph incidence.
