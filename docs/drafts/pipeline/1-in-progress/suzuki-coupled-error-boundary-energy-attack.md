# Suzuki coupled-error boundary-energy attack

- **ID:** `suzuki-coupled-error-boundary-energy-attack`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE; RH-BEARING DIRECT HILBERT--POLYA ATTACK]`
- **Source:** `../2-fully-proven/not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`;
  `../2-fully-proven/not_new_scientific_knowledge/suzuki-tail-is-exact-summatory-error-transform.md`;
  `../2-fully-proven/not_new_scientific_knowledge/shifted-euler-error-floor-mobius-tail-coupling.md`;
  `../2-fully-proven/not_new_scientific_knowledge/euler-pole-four-unit-anti-causal-budget-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/mobius-channel-critical-mass-escape-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/mobius-critical-exponential-boundary-layer-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/coupled-floor-mobius-complementary-shift-incidence-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/finite-euler-exact-differential-order-aperture-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/mobius-prime-aperture-differential-order-profile.md`;
  `../2-fully-proven/not_new_scientific_knowledge/da-gauge-ht-divisor-blindness.md`;
  `../2-fully-proven/not_new_scientific_knowledge/mobius-signed-channel-coisometry-incidence-law.md`
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
7. **Symmetric rational-gauge falsifier.** Multiplication by a centered real-even polynomial can
   insert an arbitrary finite off-critical quartet packet while preserving the functional
   equation, Schwarz reality, order one, hypertranscendence, and every finite differential
   aperture. Therefore a proposed covariance depending only on these data, on the diagonal
   Möbius norm distribution, or on a source class modulo rational/DA functions is divisor-blind.
   The proof must use a pointed exact source--divisor incidence which detects the rational
   logarithmic-derivative correction.

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

11. **The Möbius half has a canonical contractive channel realization.** After the unitary
    logarithmic change of variables, define

    ```text
    (C_omega f)_d
     =sqrt(1/zeta(1+2omega)) mu(d)d^(-1/2-omega)
       V_(log d)f.
    ```

    The squarefree Dirichlet-series identity gives the exact norm

    ```text
    ||C_omega f||^2=1/zeta(2+4omega)||f||^2.             (12c)
    ```

    As `omega` decreases to zero, every fixed divisor coordinate vanishes while the total norm
    tends to `||f||^2/zeta(2)`. Thus the critical arithmetic mass escapes through cofinally large
    divisor channels. Every fixed compact synthesis annihilates it. A faithful synthesis must be
    noncompact or cutoff-dependent in a way that explicitly tracks the growing tail.

12. **The remaining synthesis is exactly the coupled difficulty.** If

    ```text
    phi_omega(t)=1_(t>=0)e^(-t/2)g_omega^(1)(e^(-t)),
    ```

    then the causal source has the locally finite factorization

    ```text
    U h_omega^(1)
     =sum_(d,m>=1)
       mu(d)d^(-1/2-omega)m^(-1/2+omega)
       V_(log d+log m)phi_omega.                          (12d)
    ```

    The Möbius analysis in `(12d)` is channel-contracting after normalization, but the coherent
    power-sum synthesis is not an `l2` row. The archimedean moment zero and the compensating
    Möbius tail must regularize this synthesis jointly. This is the exact place where the desired
    contraction remains unproved.

13. **The escaping mass has an exact critical aperture.** Normalize the squared divisor-channel
    norms in `(12c)` to a probability law and set `Y_omega=2omega log d`. Its Laplace transform is

    ```text
    E exp(-uY_omega)
     =zeta(1+2omega(1+u))zeta(2+4omega)
       /(zeta(2+4omega(1+u))zeta(1+2omega)),
    ```

    which tends to `1/(1+u)`. Hence

    ```text
    2omega log d => Exp(1).                               (12e)
    ```

    A divisor aperture `D_omega=exp(c/(2omega))` retains the precise norm fraction
    `1-exp(-c)`. Full norm transport requires `omega log D_omega -> infinity`. Therefore a proposed
    cancellation proved only in a fixed window, or even on `log d=o(1/omega)`, controls
    asymptotically none of the Möbius input mass.

14. **The floor and tail are complementary shift incidences.** Let `P_d` be the orthogonal
    projection of `L2(R_+)` onto `[log d,infinity)`. For `delta>0`, set

    ```text
    q_delta(t)=e^(-delta t),
    k_(omega,delta)(t)
      =e^(-(1+omega+delta)t)R_omega(e^t).
    ```

    Then the exact coupled error is

    ```text
    e^(-(1+omega+delta)t)E_omega(e^t)
     =sum_(d>=1)mu(d)d^(-1-2omega)
       (
         d^(-delta)V_(log d)k_(omega,delta)
         -(1/(1+omega))(I-P_d)q_delta
       ).                                                 (12f)
    ```

    Both series converge absolutely in `L2`. At `delta=0`, the two branches have the same
    coefficient `mu(d)d^(-1-2omega)` and are selected by the complementary incidences `P_d` and
    `I-P_d`, but the common upper input becomes `1`, outside `L2`; indeed
    `||q_delta||^2=1/(2delta)`. Thus the exact coupling is a boundary form. The archimedean
    completion must renormalize this single boundary mode into `ell_pole` while retaining the
    lower/upper incidence. This is the concrete covariance/synthesis map still missing from
    `(12b)`.

15. **Finite Euler observability has exact scalar order.** For a cutoff prime set `S`, every
    first-order-faithful rational readout of the local exponential coordinates has differential
    aperture `#S`, including the Euler flux, product, inverse anchor, and finite diagonal
    determinant. The equality remains true over `C(s)<Gamma>`. The formal tree already proves the
    nonsingular weighted-Vandermonde differential in
    `RHTower.eulerSourceJetJacobian_bijective`; it does not yet contain the
    rational-function Jacobian criterion and meromorphic evaluation-field infrastructure needed
    to promote this to the complete minimal-ADE-order theorem. Adding an aperture wrapper around
    the existing bijectivity result would not formalize the missing algebraic independence.

16. **The critical norm has an exact prime-state price curve.** The fraction of normalized Möbius
    channel norm generated by primes `p<=N` is

    ```text
    M_omega(N)=product_(p>N)(1+p^(-1-2omega))^(-1).      (12g)
    ```

    For `N_omega=exp(c/(2omega))`, the prime number theorem gives

    ```text
    M_omega(N_omega)->exp(-E_1(c)),
    E_1(c)=integral_c^infinity e^(-u)du/u.                (12h)
    ```

    If `c_q` is defined by `exp(-E_1(c_q))=q`, retaining source-norm fraction `q` requires a
    first-order-faithful scalar aperture

    ```text
    ap_q(omega)
      ~ (2omega/c_q)exp(c_q/(2omega)).                   (12i)
    ```

    Full norm transport is equivalent to `2omega log N_omega->infinity` and forces
    `omega log ap(omega)->infinity`. Thus the required cofinal state is quantitatively larger than
    any fixed-order or polynomial-order approximation; bounded-exponent `exp(O(1/omega))` syntax
    retains strictly less than the full critical source.

17. **The carrier must be marked by an orbit-sensitive source--divisor incidence.** Let `A` be a
    centered real-even polynomial whose zeros are a finite off-critical quartet packet. Replacing
    `Xi` by `Xi_A=A Xi` changes the tangent logarithmic source by

    ```text
    -2 Dlog Xi_A=-2 Dlog Xi-2 Dlog A,                    (12j)
    ```

    while the anti-causal contour-jump profile changes by the explicit signed residue vector
    `J_A` of the inserted right-half zeros. Consequently any genuine source-to-boundary map `T`
    must obey
    the gauge covariance

    ```text
    T(source_Xi-2Dlog A)-T(source_Xi)=J_A.                (12k)
    ```

    A map which kills rational/DA corrections or sees only the diagonal squared channel weights
    would instead give `J_A=0`, contradicting the
    formalized quartet countermodel in `XiRationalQuartetGauge.lean`. Thus `(12c)`--`(12i)` fix the
    size of the carrier but cannot prove RH: the missing covariance must retain the signed Möbius
    phases and the exact normalization tying that source to the distinguished Xi divisor.

18. **The pointed arithmetic projection is explicit.** Normalize

    ```text
    P_omega(d)
      =mu(d)^2d^(-1-2omega)
        /sum_n mu(n)^2n^(-1-2omega)
    ```

    and define the signed coisometry

    ```text
    R_omega((f_d))
      =sum_d sgn(mu(d))sqrt(P_omega(d))f_d.
    ```

    Then `R_omega R_omega^*=I`, so

    ```text
    Pi_omega=R_omega^*R_omega
    ```

    is an orthogonal projection onto the distinguished signed source line in the divisor-channel
    index. If `Y_omega` is the exact complementary floor--tail feature from `(12f)` and

    ```text
    Z_omega=sum_d mu(d)^2d^(-1-2omega),
    F_omega(t)=e^(-(1+omega)t)E_omega(e^t),
    ```

    then

    ```text
    F_omega=Z_omega R_omega Y_omega,
    ||F_omega||=Z_omega||Pi_omega Y_omega||.             (12l)
    ```

    Moreover, channelwise support orthogonality gives the exact ambient norm

    ```text
    ||Y_omega||^2
      =||k_omega||^2
       +(1+omega)^(-2)(
         -zeta'/zeta(1+2omega)
         +2zeta'/zeta(2+4omega)
       ).                                                (12m)
    ```

    Hence the coupled cancellation is exactly an angle-to-source-line theorem. The prime-aperture
    laws control the ambient norm and where it lives; the RH-bearing residue is the critical decay
    of the projected component after archimedean boundary renormalization.

19. **Closed channelwise continuation commutes with the signed synthesis.** For any closed linear
    operator `G` on the one-channel Hilbert carrier, let `G^(direct sum)` have the graph-norm domain

    ```text
    sum_d(||f_d||^2+||Gf_d||^2)<infinity.
    ```

    Finite channel sums commute with `G`; boundedness of `R_omega` and closedness of `G` pass the
    identity to the graph limit. Therefore

    ```text
    G R_omega f=R_omega G^(direct sum)f.                 (12n)
    ```

    No additional covariance estimate is lost in the channel synthesis. The remaining domain
    theorem is concrete: represent Suzuki's signed archimedean Stieltjes/Mellin operator as a
    closed operator `G_omega` on the chosen carrier and prove
    `Y_omega in D(G_omega^(direct sum))` with the critical graph-norm control.

20. **Ordinary-Hardy continuation is now formally excluded; the charged graph is mandatory.**
    `OrbitSensitiveContinuationCharge.lean` proves the actual one-pole identities

    ```text
    integral_R |q_(a,gamma,c)(x+iY)|^2 dx=pi|c|^2/(Y-a),
    integral_0^infinity |Jq_(a,gamma,c)(t)|^2dt=|c|^2/(2a),
    ```

    their exact ratio `(Y-a)/(2 pi a)`, and a quantified theorem that no finite fixed-line energy
    constant controls every `a downarrow 0`. Any bounded residue graph with bound `M` is forced to
    put at least `(|c|^2/(2a))/M^2` into its domain budget. The same module identifies the two
    right-half modes with actual zeros of the formalized centered FE--Schwarz quartet gauge and
    proves their exact residue energy

    ```text
    4m^2/a+4m^2 a/(a^2+gamma^2) >= 4m^2/a.              (12o)
    ```

    Therefore `(12b)` cannot mean bounded continuation from an ordinary Euler-line Hardy norm.
    It must mean nonexpansive renormalization inside a graph norm which has already paid the
    inverse-horizontal charge. Merely asserting the existence of some contraction taking
    `ell_pole` to `ell_E` is equivalent to the desired norm inequality and has no independent
    content. The live theorem must construct the graph and the renormalization from the exact
    coupled source before reading `ell_E` as a divisor expansion.

21. **The rank-two Cauchy kernel is an exact endpoint, not a source producer.** The concurrent
    `XiWeilCauchyPoleExhaustion.lean` theorem proves

    ```text
    RH iff every regular two-pole Cauchy packet has nonnegative Xi--Weil square.
    ```

    `XiWeilResolventSource.lean` identifies each separated packet entry with the divided difference
    of `continuedPrimeArchSourceRelativeTrace`. Thus the corresponding two-by-two source kernel is
    a minimal Hilbert--Pólya endpoint: a source Gram factorization of that kernel would prove RH.
    But its positivity cannot be imported as a property of the continued trace, because the
    pole-exhaustion theorem proves that this positivity is already equivalent to RH. Generalized
    Pick/Krein--Langer theory supplies the coordinate and counts negative squares; it does not
    remove them. The positive construction obligation is therefore to build the two-vector Gram
    factorization from the coupled Euler--Gamma carrier before using the Xi divisor. This is the
    rank-two resolvent form of the same charged-graph seam, not a separate CCM shortcut.

22. **The all-prime causal arithmetic channel and its exact multiplier are now formal.**
    `InfiniteMobiusCausalShift.lean` proves that every positive logarithmic right shift preserves
    zero-threshold causal `L^2`, and that the absolutely summable Möbius average preserves it.
    `InfiniteMobiusLaplaceMultiplier.lean` then proves, for `sigma>1` and `x>0`,

    ```text
    L_x(T_sigma f)=tau_sigma(x)L_x(f),
    tau_sigma(x)=zeta(2sigma)/
      (zeta(sigma)zeta(sigma+pi*x)).                    (12p)
    ```

    Here `T_sigma` is the actual signed all-prime logarithmic shift average, already proved
    contractive on ambient `L^2`; no formal scalar multiplier or finite cutoff remains. This is
    the positive carrier forced by the Möbius normalization: a successful construction must
    extend `(12p)` from the causal half-plane to the common Xi-pointed charged graph while coupling
    the floor discrepancy through the archimedean kernel. The remaining theorem is not the Euler
    multiplier identity; it is the nonexpansive charged continuation that converts this exact
    arithmetic factor into the pole-to-divisor transfer `(16)`.

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

Here "source-defined" includes the marking condition `(12k)`. The operator cannot be constructed
only from the prime-support aperture, the diagonal channel norm, FE symmetry, reality, growth, HT,
or differential aperture: all of those survive a symmetric orbit insertion. It must couple the
exact weighted all-prime tail and archimedean completion to the distinguished divisor/trace
moments, in a topology strong enough to retain the contour-jump residues.

The arithmetic part of the pointed projection candidate `(10)` is therefore no longer
conjectural. `InfiniteMobiusSignedChannel.lean` realizes the normalized all-prime amplitude as an
actual unit vector in `ell^2(N)`, proves that `R_omega` is a surjective coisometry, and proves that
`Pi_omega=R_omega^*R_omega` is a contractive idempotent projection. This removes the finite-cutoff
surrogate from `(12l)`. The causal-shift and Laplace-multiplier modules prove that its signed
logarithmic translation average preserves the causal Hardy carrier and has the exact normalized
reciprocal-zeta multiplier `(12p)`. What remains is the archimedean continuation to the common
doubled charged graph, the coupled floor-discrepancy cancellation, and the critical estimate
converting `(12l)` into the pole-to-divisor contraction `(16)`.

The coupled derivative `2(psi-X)` is the arithmetic coordinate of this replacement.  Any
finite-prime autonomous ADE implementation retaining `{log p:p<=N}` must additionally expose
Kolchin jet capacity at least `ceil(pi(N)/2)`; otherwise `(16)` must live in one of the genuinely
infinite/global carriers listed by the singular Kolchin-frequency theorem.

On the rational first-order-faithful Euler face, the stronger exact differential-aperture theorem
applies. For every finite prime set `S`, the Euler logarithmic flux, Euler product, inverse anchor,
and finite diagonal determinant obey

```text
ap_C(E_S)=ap_C(Z_S)=ap_C(A_S)=#S,
ap_(C(s)<Gamma>)(E_S)=#S.                                (17)
```

Thus the canonical cutoff has

```text
ap(E_(S_N))=pi(N).                                       (18)
```

In this class each prime costs exactly one scalar differential order; the earlier Kolchin
half-rank inequality is only the general singular fallback. Consequently a scalar rational
readout of the finite transfer `(16)` must have order exactly `pi(N)` whenever it remains
first-order sensitive to every Euler coordinate. Determinant formation and Gamma completion may
package the coordinates, but cannot reduce this order.

For nonautonomous implementations the sharper coefficient--state conservation law applies.  If
`Gamma(a)` is the coefficient-hull frequency module and `kappa_rel` is the relative Kolchin
capacity of the solution fiber, then

```text
A_N=V_N/(V_N intersection Gamma(a)),
dim_Q A_N<=2 kappa_rel.                                  (19)
```

Consequently every new prime direction must be paid exactly once through growing differential
order, growing algebraic degree/jet capacity, coefficient-side frequency, or genuinely
infinite-dimensional state.  This is an admissibility condition on a construction of `(16)`, not
a substitute for its nonexpansive estimate.

The bounded-syntax theorem makes the scalar clause uniform. If `P_N` has order `n_N` and degree
`d_N`, then

```text
rank_Q Gamma(f_N)<=2B(n_N,d_N).
```

Faithful cofinal prime transport therefore forces

```text
max(n_N,d_N) -> infinity,
```

unless the missing capacity is visibly stored in growing arity, coefficient-side frequency,
infinite-dimensional state, a global constraint, or a separately justified noncompact carrier.
The mass-escape law `(12c)` identifies the last alternative concretely for the Möbius source: its
critical norm survives only in cofinally large divisor coordinates.

Together, `(17)`--`(19)` impose a sharper design condition on the missing synthesis/covariance.
At cutoff `N` it must expose a first-order-faithful prime incidence of aperture `pi(N)` before the
archimedean boundary renormalization. If it is scalarized earlier, its differential order is
exactly `pi(N)`; if its scalar syntax stays bounded, the same `pi(N)` coordinates must remain
visible in the operator domain, coefficient hull, determinant/divisor object, or another genuinely
non-scalar state. The source-defined contraction cannot quotient them away before taking the
cofinal strong limit.

Only after this operator is constructed is there a legitimate Lean target.  Formalizing
`(1) -> RH` with `(1)` as a hypothesis would be a wrapper around the existing energy criterion.

## Gates

- [x] exact RH-bearing norm target fixed
- [x] coupled floor/Mobius source fixed
- [x] critical derivative law `(5)` proved
- [x] causal-source/anti-causal-defect distinction proved
- [x] finite-energy reduction `(12)`--`(14)` proved
- [x] all-prime causal Möbius shift channel and exact reciprocal-zeta multiplier `(12p)` proved
- [ ] distributional critical limit of the completed transform
- [ ] pointed projection, sum rule, or renewal contraction
- [ ] unconditional boundary norm `(1)`
- [ ] end-to-end Lean proof of RH
