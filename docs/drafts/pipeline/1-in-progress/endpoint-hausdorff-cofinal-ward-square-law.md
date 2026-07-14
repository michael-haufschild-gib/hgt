# Endpoint Hausdorff cofinal Ward-square law

- **ID:** `endpoint-hausdorff-cofinal-ward-square-law`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] RH route; source-pure cofinal estimate`
- **Source:** endpoint-calibrated source--temperature master theorem
- **Statement:** `[CONJECTURE]` The complementary calibrated differences admit one all-order
  theta-source Ward decomposition whose bulk terms are nonnegative squares and whose boundary
  term has a source-side sign; consequently every `D^*_{k,r}` is nonnegative.

## Goal

Prove the remaining condition

\[
\mathsf T_*:\qquad
D^*_{k,r}\ge0\quad(k>13\text{ or }r>43),
\]

where

\[
D^*_{k,r}=\sum_{j=0}^r(-1)^j\binom rjR_*^{r-j}\mu_{k+j}
=\Re\sum_\rho\lambda_\rho^{k+1}(R_*-\lambda_\rho)^r.
\]

The formal master theorem already proves `T_* <-> RH`; therefore only an unconditional source-side
identity and sign argument counts as progress.  A decomposition obtained from assumed Hankel,
Hausdorff, KMS, or RH positivity is circular.

## Competing moves

1. `[CONJECTURE] Ward-square transform.`  Express the polynomial functional
   `p(X)=X^k(R_*-X)^r` of the normalized prime--Gamma germ through the theta cusp density and use
   the all-order Liouville/Witten Ward identities to integrate it into squares plus a boundary
   term.
2. `[CONJECTURE] Source localizer.`  Construct one positive differential or integral localizing
   operator `L_*` on the theta half-line such that
   `D^*_{k,r}=<L_*^k u_r,u_r>` or an equivalent reflection-positive quadratic form.
3. `[CONJECTURE] Cofinal determinant propagation.`  Derive the calibrated Hausdorff tail from a
   source recurrence with nonnegative coefficients.  This is admissible only if the recurrence is
   obtained independently from the Euler--Gamma source, not from the target moment determinants.
4. `[BRIDGE / LIKELY DEAD] Finite verified-height dominance.`  A verified critical-line prefix can
   force additional finite positivity, but cannot prove the cofinal tail and is not the main route.

## Hard attacks

- Positive theta density alone does not orient nonlinear cumulants; the low-order cumulant formulas
  already contain forced negative terms.
- A generic Hamburger/Hausdorff representation is equivalent to the desired positivity and cannot
  be used as input.
- Reflection-positive Hankel machinery transports positivity but does not create the arithmetic
  sign.
- Any finite rectangle can be defeated by a sufficiently remote off-line quartet; the required
  identity must be all-order or cofinal.
- The Ward transform fails if its boundary term is an uncontrolled copy of the original
  `D^*_{k,r}` or if a coefficient changes sign at unbounded order.

## Physics-lane audit

The current formal tree supplies three distinct layers which must not be conflated.

1. **Unconditional quantitative layer.**  The endpoint quartet estimates give
   
   \[
   \mathcal E_\perp<\frac1{150000},\qquad
   \mathcal E_\perp\le \frac1{84}\mathcal M_2,
   \]
   
   together with the self-localized cubic bound in the off-line endpoint charge.  These are real
   estimate gains, but no positive gap separates a remote off-line quartet from zero charge.
2. **Exact detector layer.**  The faithful projective partition
   
   \[
   Z_N(\beta)=\sum_{j<N}w_j e^{\beta\delta_j},
   \qquad w_j>0,
   \quad \delta_j=\left|\Re\rho_j-\frac12\right|,
   \]
   
   is monotone in both coordinates.  Along every cofinal size/cooling schedule its normalized
   logarithm has the exact limit

   \[
   \frac{\log Z_{N_j}(\beta_j)}{\beta_j}\longrightarrow\delta_*.
   \]

   Thus RH is equivalent to subexponential growth along any one such section; boundedness is a
   strictly stronger presentation of the same endpoint.  This is the correct positive thermal
   carrier, not a finite-temperature sign test.
3. **Prime-source realization layer.**  Finite prime-log Hermitian Gibbs responses now converge
   jointly as cutoff and inverse temperature tend to infinity, locally uniformly on the upper
   half-plane and in every holomorphic jet.  The uniform input is the spectral gap `log 2` and the
   finite dyadic prime mass.  This constructs a cofinal prime carrier but does not yet couple it to
   the Xi projective partition.

The exact missing physics theorem is therefore positive and source-specific:

`[CONJECTURE]` **Cofinal source--divisor Gibbs subexponential domination.**  Construct from the
completed prime--Gamma source a cofinal schedule `(N_j,beta_j)` and explicit source values `B_j`
such that, for every `epsilon > 0`, eventually

\[
Z_{N_j}(\beta_j)\le B_j\le e^{\varepsilon\beta_j},
\]

with the first inequality proved by an exact source/divisor value relation rather than by assumed
RH, passivity, reflection positivity, Hausdorff positivity, or thermal moment closure.  This is
the weakest exact thermodynamic endpoint supplied by the present architecture and would
immediately imply RH through the free-energy radius law.

The Born--Witten/Morse--Fisher lane supplies a separate finite-degree source estimate: every
linear trace--Hankel test follows from rational enclosures for `exp(-pi)` and the first nine moments
of one positive incomplete-Gamma density.  Those enclosures remain unproved, and even their proof
would close only the first nonconstant Hankel block, not the cofinal Hausdorff tail.

## Gates

- [x] 0 → 1 in-progress: exact cofinal target, source-pure candidates, and circularity firewall stated
- [ ] identify the all-order source operator representing `D^*_{k,r}`
- [ ] construct or rule out a source-pure comparison from the joint prime-log Gibbs limit to one
      cofinal Xi projective cold section
- [ ] prove an exact Ward/localizer identity for every `k,r`
- [ ] prove every bulk coefficient and boundary contribution has the required sign
- [ ] derive `PrimeArchEndpointHausdorffTailNonnegative` without RH-equivalent assumptions
- [ ] 1 → 2 fully-proven: complete paper proof with no open dependency
- [ ] 2 → 3 formalized: unconditional Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: integrate the proof into the master paper

## Log

- 2026-07-14 — created after the unconditional `14 x 44` rectangle reduced the route to one
  complementary cofinal tail.
- 2026-07-14 — physics-lane audit isolated the exact cofinal source--divisor Gibbs domination
  theorem; current KMS, passivity, Krylov, and cold-partition results do not supply that comparison.
