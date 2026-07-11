# Suzuki coupled-error boundary-energy attack

- **ID:** `suzuki-coupled-error-boundary-energy-attack`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE; RH-BEARING DIRECT HILBERT--POLYA ATTACK]`
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  `../2-fully-proven/not_new_scientific_knowledge/suzuki-tail-is-exact-summatory-error-transform.md`;
  `../2-fully-proven/not_new_scientific_knowledge/shifted-euler-error-floor-mobius-tail-coupling.md`;
  `../2-fully-proven/not_new_scientific_knowledge/euler-pole-four-unit-anti-causal-budget-law.md`
- **Target:** Prove directly from the completed Euler--Gamma source that the first-order
  anti-causal profile `ell_E` satisfies

  ```text
  integral_0^infinity |ell_E(t)|^2 dt <= 4.                 (1)
  ```

  The existing positive Cauchy-energy theorem then proves RH.

## 1. Exact coupled arithmetic source

For `omega>0`, put

```text
c_omega(n)
 =n^omega product_(p|n)(1-p^(-2omega)),

A_omega(X)=sum_(n<=X)c_omega(n),

M_omega(X)
 =X^(1+omega)/((1+omega)zeta(1+2omega)),

E_omega(X)=A_omega(X)-M_omega(X).                         (2)
```

The source identity already proved in the corpus is

```text
h_omega^(1)(x)
 =x^(-1) integral_((0,x])
    g_omega^(1)(t/x)dE_omega(t).                          (3)
```

The two terms of the exact arithmetic decomposition are

```text
E_omega(X)
 =sum_(d<=X)mu(d)d^(-omega)R_omega(X/d)
  -X^(1+omega)/(1+omega)
    sum_(d>X)mu(d)d^(-1-2omega),                         (4)

R_omega(Y)
 =sum_(m<=Y)m^omega-Y^(1+omega)/(1+omega).
```

They are not to be estimated separately.  Their coupling is the source constraint.

## 2. Critical derivative law `[PROVED HERE; BRIDGE]`

Let

```text
psi(X)=sum_(n<=X)Lambda(n).
```

At every fixed `X>=1`, the right derivative at `omega=0` is

```text
partial_omega E_omega(X)|_(0+)
 =2(psi(X)-X).                                            (5)
```

### Proof

For fixed `X`, the sum defining `A_omega(X)` is finite.  The coefficient theorem gives

```text
partial_omega c_omega(n)|_0=2Lambda(n),
```

including the value zero at `n=1`.  Hence

```text
partial_omega A_omega(X)|_0=2psi(X).                      (6)
```

The Laurent expansion of zeta at one gives

```text
1/zeta(1+2omega)=2omega+O(omega^2).                       (7)
```

Since

```text
X^(1+omega)/(1+omega)=X+O_X(omega),                       (8)
```

equations `(7)`--`(8)` imply

```text
partial_omega M_omega(X)|_(0+)=2X.                        (9)
```

Subtracting `(9)` from `(6)` proves `(5)`.

This is a coordinate bridge, not an RH advance by itself: pointwise or mean-square control of
`psi(X)-X` at the critical exponent is classically RH-bearing.

## 2A. Causal source versus anti-causal defect `[PROVED; SEARCH/BRIDGE]`

The coupled transform `(3)` is not itself the infinitesimal anti-causal profile. Suzuki's exact
Mellin identity is

```text
integral_0^infinity h_omega^(1)(x)
  x^(1/2+i z) d*x
 =i Theta_omega(z)/z,
Im z>1/2+omega.                                           (9a)
```

Define the causal residual on `x>1` by

```text
r_omega(x)=x^(-1/2)-h_omega^(1)(x).                       (9b)
```

Suzuki's Theorem A.1 proves

```text
r_omega in L2((1,infinity),dx)
 <-> Theta_omega is inner in the upper half-plane
 <-> zeta has no zero with Re rho>1/2+omega,              (9c)
```

with the usual common-divisor convention. When innerness holds, Mellin--Plancherel identifies
`r_omega` with the boundary inverse transform of

```text
(1-Theta_omega(z))/(i z).                                 (9d)
```

Without innerness, shifting the contour from the Euler line to the Hardy boundary crosses the
upper-half-plane poles of `Theta_omega`; the crossed residues are precisely the anti-causal
off-line-zero modes. Therefore the formal move

```text
differentiate the causal error transform `(3)` at omega=0
  = the infinitesimal anti-causal profile
```

is false without an additional contour-jump theorem. Proving the `L2` cancellation in `(9c)` for
all positive `omega` is already RH, not an easier estimate from which `(1)` follows formally.

The legitimate critical object is the difference between two continuations of the same source:

```text
critical boundary inverse
  - Euler-line causal continuation
  = anti-causal contour-jump defect.                      (9e)
```

The requested norm `(1)` is the first-order energy of `(9e)`, not the norm of either term alone.

## 3. Candidate mechanisms

### Candidate A: pointed Nyman projection

`[CONJECTURE]` After logarithmic change of variables and distributional differentiation of `(3)`
at `omega=0`, there are a fixed vector `v_arch` of squared norm `4`, a Hilbert space `H_src`, and
a source-defined orthogonal projection `P_src` such that

```text
ell_E=P_src v_arch.                                       (10)
```

Then `(1)` follows from projection contractivity.  The projection must preserve the marked
Möbius/floor coupling in `(4)`; an abstract unitary image or an unpointed Nyman closure is
insufficient.

After `(9e)`, `P_src` must act on the two-continuation incidence graph. A projection constructed
only from the causal Nyman/Suzuki residual would assume `(9c)` and be circular.

### Candidate B: completed Hardy sum rule

`[CONJECTURE]` The second-order Toeplitz curvature has a boundary sum rule

```text
C_E(0,0)+B_causal=B_arch,                                 (11)
```

where `B_causal>=0` and `B_arch=4` are constructed before a divisor expansion.  Equation `(11)`
would give `(1)`.  The generic self-dual-quartet counterexample proves that `(11)` must use the
exact Euler coefficients, not only FE symmetry and boundary unimodularity.

### Candidate C: completed renewal contraction

`[CONJECTURE]` The two summands in `(4)`, after applying the signed archimedean Stieltjes kernel,
are the input and boundary counterterm of one contractive renewal operator.  Its defect vector is
`ell_E`, and the renewal input has squared norm `4`.

## 4. Mandatory attacks

1. **Distributional seam.** At `omega=0`, the Mellin kernel contains the identity mass at `x=1`.
   Differentiating `(3)` termwise is invalid until the delta contribution and the derivative of
   `g_omega^(1)` are combined.
2. **Nyman circularity.** If `(10)` is merely the classical Nyman--Beurling projection onto the
   full zeta-generated closure, proving that the target lies in the range is RH.  The projection
   must follow from an unconditional source orthogonality or a smaller closed range.
3. **Boundary evaluation.** Toeplitz contractivity controls operator norm but not the corner
   `C_E(0,0)`; the one-layer model makes the corner unbounded.  Any proof of `(11)` needs a genuine
   trace or reproducing-kernel domain theorem.
4. **Separate estimates.** Absolute values in `(4)` stop at `X^(1-omega)` and destroy the required
   cancellation.
5. **Divisor reconstruction.** Expanding `ell_E` into Xi-zero residue modes proves the implication
   from `(1)` to RH but cannot prove `(1)`.
6. **Wrong-side identification.** The pole-subtracted summatory error determines the Euler-line
   causal primitive. The energy target lives in the contour jump `(9e)`. A coupled-cancellation
   proof must control the difference of the two continuations, not merely estimate `(3)`.

## 4A. Finite-energy reduction `[PROVED HERE; BRIDGE]`

Let `J` be any finite set of distinct right-half zero locations

```text
rho_j=1/2+a_j+i gamma_j,
0<a_j<1/2,
```

with multiplicities `m_j>=1`, and let

```text
ell_J(t)=2 sum_(j in J)m_j exp(-(a_j+i gamma_j)t).
```

Then the Cauchy Gram identity gives

```text
||ell_J||_2^2
 =4 sum_(j,k in J)m_j m_k
   (a_j+a_k)/((a_j+a_k)^2+(gamma_j-gamma_k)^2)

 >4 sum_(j in J)m_j^2
 >=4 #J.                                                   (12)
```

All ordered-pair contributions are positive, and the diagonal contribution is
`2m_j^2/a_j>4m_j^2`. Hence the finite-subset energies are monotone under enlargement and diverge
for an infinite right-half divisor. Consequently

```text
finite first-order contour-jump energy
  -> only finitely many off-line zeros,                    (13)

energy <=4
  -> no off-line zero
  -> RH.                                                   (14)
```

This splits the source problem into two positive carrier theorems:

1. source boundary regularity makes the contour-jump energy finite;
2. exact Euler discreteness excludes a finite nonzero contour-jump divisor.

The second theorem is not in the current corpus. Existing quiet-crossing rigidity saturates at the
degree-one Gamma boundary, and sparse-Euler divisor rigidity requires a comparison Euler product
not supplied by finite-exception factorization.

## 4B. Wide corpus and Lean audit `[COMPLETED 2026-07-11]`

The project already contains most of the functional-analytic shell required by a proof.

1. **Exact incoming vector and norm.** `EulerPoleBoundaryBudget.lean` defines the canonical
   `L2(R)` vector represented by `2 exp(-t/2)` on `t>0` and proves

   ```text
   ||eulerPoleBoundaryProfileL2||^2=4.                    (12a)
   ```

   This reuses the exact Cauchy inner product in `XiThetaSquareRateLaplace.lean`.

2. **Closed causal support under strong `L2` convergence.** The continuous restriction map
   `negativeHalfLineRestrictionL2` and
   `hasAELowerSupport_zero_iff_negativeHalfLineRestrictionL2_eq_zero` in
   `XiThetaSquareRateCausalSource.lean` already prove the required closed-support mechanism.

3. **A complete finite-to-boundary prototype.** The theta square-rate files prove finite causal
   source construction, pointwise boundary convergence, a common Cauchy majorant, dominated
   convergence of squared differences, strong `L2` convergence, and preservation of causal
   support. This is exactly the topology pattern required here. Its decisive input is that every
   finite factor is Blaschke-contracting on the right half-plane. Prime Euler factors do not have
   that property, so the selected-factor estimate cannot simply be renamed.

4. **Exact source continuation.** `XiRelativeResolventFlux.lean` proves that the continued
   von-Mangoldt plus archimedean trace equals the Xi relative resolvent away from natural poles.
   This supplies the target identification but not convergence of a finite-prime exhaustion at the
   critical boundary.

5. **Canonical two-line defect.** `CanonicalPerronMellinSeam.lean` constructs a unique additive
   cross-line `L2` defect whenever the carrier line has finite flank energy; it also proves
   source-gauge invariance and coefficient recovery. Thus the seam need not be postulated once the
   missing energy estimate is known.

6. **Correct doubled geometry.** `SeamKreinStructure.lean` proves the reciprocity graph is
   Lagrangian for the signed doubled form and that one-particle prime reflection is unbounded.
   Therefore the transfer belongs in a doubled domain/closure defect, exactly as `(9e)` requires.

7. **Arithmetic algebra already present.** `MertensFirst.lean`, `Mollifier.lean`,
   `MollifierDetection.lean`, and `PrimeLambertMobiusInversion.lean` formalize von-Mangoldt divisor
   swaps and absolute Mobius inversions. They do not formalize the shifted coefficient
   `c_omega`, the coupled error `E_omega`, or Suzuki's signed archimedean kernel.

8. **Infinite-dimensional carrier exists but is not the transfer.** The all-prime Sonin residual
   and coupled-column modules construct Hilbert--Schmidt all-prime operators and positive
   trace-class energies retaining cross-prime overlaps. Their known missing theorem is an
   identification with the Xi boundary object; they do not couple the Euler-pole channel to
   `(9e)` and therefore do not prove `(1)`.

9. **Downstream cofinal RH transfer is complete.** `PrimeEnergyZeroTransfer.lean` proves that
   locally uniform Xi approximants with sub-log-square zero-fibre prime energy imply RH. It is a
   consumer after the present boundary theorem, not a producer of its norm bound.

10. **A second direct finite-prime source is under concurrent development.** The current
    `ThetaCuspFinitePrimeSource.lean` constructs smooth-integer finite-prime theta-cusp states and
    proves pointwise convergence. Its own header correctly leaves compact-local convergence, the
    cofinal screen, and zero-fibre energy open. No claim from that lane supplies `(1)` yet.

The audit therefore isolates one zeta-specific construction theorem, with two inseparable clauses:

```text
construct source-defined operators S_N on one common doubled graph domain,
||S_N||<=1,
S_N ell_pole -> ell_E strongly in L2(0,infinity).          (12b)
```

Strong convergence and the formalized norm `(12a)` then give `(1)`. The exact coupled
floor-discrepancy/Mobius-tail formula must supply both the contractive majorant and the convergence;
the rest of the closure, support, seam, and RH-transfer chain is already in the corpus.

## 5. Open core

`[OPEN CORE]` Construct the critical distributional limit of `(3)` as one closed Hilbert-space
operator on the coupled pair `(4)` together with the boundary-continuation map. Prove a source
bound on the contour jump `(9e)`, not merely the causal residual `(9b)`. Equivalently, prove either
the pointed two-continuation projection identity `(10)` or the source sum rule `(11)` without using
a zero-free half-plane beyond `Re s>1`, an RH-equivalent Nyman closure statement, or a divisor
expansion.

The exact incoming budget is now known.  At every finite prime cutoff the only anti-causal channel
of the completed logarithmic tangent is the uncancelled Euler pole `s=1`, with profile

```text
ell_pole(t)=2 exp(-t/2),       ||ell_pole||_2^2=4.         (15)
```

The all-prime continuation cancels `(15)` and replaces it by `ell_E`.  Therefore the requested
bound is exactly the construction of a source-defined nonexpansive pole-to-divisor transfer

```text
ell_E=S_E ell_pole,             ||S_E||<=1.               (16)
```

The coupled derivative `2(psi-X)` is the arithmetic coordinate of this replacement.  Any
finite-prime autonomous ADE implementation retaining `{log p:p<=N}` must additionally expose
Kolchin jet capacity at least `ceil(pi(N)/2)`; otherwise `(16)` must live in one of the genuinely
infinite/global carriers listed by the singular Kolchin-frequency theorem.

For nonautonomous implementations the sharper coefficient--state conservation law applies.  If
`Gamma(a)` is the coefficient-hull frequency module and `kappa_rel` is the relative Kolchin
capacity of the solution fiber, then

```text
A_N=V_N/(V_N intersection Gamma(a)),
dim_Q A_N<=2 kappa_rel.                                  (17)
```

Consequently every new prime direction must be paid exactly once through growing differential
order, growing algebraic degree/jet capacity, coefficient-side frequency, or genuinely
infinite-dimensional state.  This is an admissibility condition on a construction of `(16)`, not
a substitute for its nonexpansive estimate.

Only after this operator is constructed is there a legitimate Lean target.  Formalizing
`(1) -> RH` with `(1)` as a hypothesis would be a wrapper around the existing energy criterion.

## Gates

- [x] exact RH-bearing norm target fixed
- [x] coupled floor/Mobius source fixed
- [x] critical derivative law `(5)` proved
- [x] causal-source/anti-causal-defect distinction proved
- [x] finite-energy reduction `(12)`--`(14)` proved
- [ ] distributional critical limit of the completed transform
- [ ] pointed projection, sum rule, or renewal contraction
- [ ] unconditional boundary norm `(1)`
- [ ] end-to-end Lean proof of RH
