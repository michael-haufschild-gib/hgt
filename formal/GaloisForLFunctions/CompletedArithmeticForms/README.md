# Quantitative theory of completed arithmetic forms

Namespace `GaloisForLFunctions.CompletedArithmeticForms`; umbrella `CompletedArithmeticForms.lean`.

**Question.** Which relations in an explicit arithmetic or theta source give a lower bound for its
complete signed form, and preserve that bound through the compression, accumulation, and limits
needed by its arithmetic conclusion?

A completed form retains the terms that can alter its sign: prime and archimedean contributions,
polar coordinates, boundary terms, and mixed entries. Its positive components are comparison
objects. The programme studies inequalities connecting those components to the original form.

**Motivation.** A positive block can lose its reserve to a Schur complement; accumulation creates
off-diagonal covariance; smoothing can destroy sharp-source recovery; fixed-parameter convergence
can fail along the exhaustion required by a criterion. Exact source identities and positive finite
sections therefore require quantitative transfer theorems.

## Objects and language

| Object | Mathematical data |
|---|---|
| Source | An explicit prime, divisor, theta, or causal distribution with its exact identities |
| Domain | The finite packet, test space, or summability class on which the form is defined |
| Complete form | A signed quadratic or sesquilinear form retaining every source contribution |
| Comparison form | A nonnegative form identified directly from the source |
| Radical | Null directions requiring separate treatment |
| Reserve | A quantitative lower bound in a stated norm or on a stated quotient |
| Completion cost | The remainder, mixed block, or boundary term between source and comparison forms |
| Transfer | A proved identity or inequality under a specified map of source domains |
| Exhaustion | A simultaneous range of rank, conductor, aperture, horizon, or cutoff |
| Endpoint tolerance | Positivity, semiboundedness, finite index, a count error class, or a census allowance |

A **source comparison** bounds the complete form by a controlled quantity on its natural domain.
A **relative estimate** measures a remainder against the reserve it consumes. A **successor reserve**
is the Schur complement permitting enlargement of a positive section. A **completion domain**
specifies which infinite signed combinations are legitimate.

These terms supply no positivity assumptions. A structure containing the missing source inequality
as a field has not proved that inequality.

## Mechanisms

**Arithmetic Gram completion.** Primitive cyclotomic prefixes give a genuine overlap Gram.
A divisor family yields an explicit discrete bridge kernel. Exact radicals and inverse operators
can turn this identity into a norm estimate.

**Successor compensation.** A strict finite section has a native source Schur integral.
A reusable identity must control this integral as rank grows, or control any developing radical.

**Signed completion on a domain.** A difference of positive Grams can represent a complete source.
Its negative channel must be paid by terms present in that source. Divergent channels cannot be
assigned an unrestricted positive finite part.

**Accumulation and covariance.** Summing divisor coefficients before measuring their error creates
a new quadratic form. Its unequal-pair terms and infinite tail belong to the estimate.

**Quantitative transfer.** Compression, interpolation, inversion, and cutoff changes carry norms
and constants. The endpoint determines which losses are permissible.

**Signed dispersion.** A centered correlation functional may admit a useful upper bound without
individual correlation asymptotics. Its window, centering, parity, and normalization remain fixed.

## Foundational theorems in the corpus

1. **Cyclotomic Gram and radical.** For primitive-prefix Grams $G_m$,
   $$
   \sum_{i,j}a_i a_jG_m(k_i,k_j)
   =\sum_{\zeta\ {\rm primitive}\ m}\left|\sum_i a_i\sum_{r<k_i}\zeta^r\right|^2.
   $$
   Vanishing is equivalent to divisibility of the prefix polynomial by $\Phi_m$.
   See [Gram completion](../CriticalArithmeticCorrelationTheory/TheArithmeticCurvatureHasAnExactGramCompletion.lean)
   and [radical classification](../CriticalArithmeticCorrelationTheory/CyclotomicDivisibilityClassifiesTheOverlapGramRadical.lean).

2. **Divisor completion.** For $0\le i,j\le Q$,
   $$
   \sum_{m\mid Q,\ m\ne1}G_m(i,j)=Q\min(i,j)-ij.
   $$
   See [AllDivisorConductorsRecoverTheDiscreteBridge](../CriticalArithmeticCorrelationTheory/AllDivisorConductorsRecoverTheDiscreteBridge.lean).
   This fixes the actual arithmetic comparison kernel, including its cross entries.

3. **Prime packet uniformity.** At fixed modulus, one prime-window horizon controls every finite
   complex residue Gram packet. Affine multiplier and shift can vary arbitrarily with the horizon.
   See [PrimeResidueWindowsControlEveryGramPacket](../CriticalArithmeticCorrelationTheory/PrimeResidueWindowsControlEveryGramPacket.lean)
   and [ActualAffinePrimeWindowsAreUniformInTheirParameters](../CriticalArithmeticCorrelationTheory/ActualAffinePrimeWindowsAreUniformInTheirParameters.lean).

4. **Signed theta sections.** For $s_a(2n)=(-1)^n k_a^{(2n)}(0)$, $s_a(2n+1)=0$, the full
   $H_{a,7}=[s_a(i+j)]_{i,j<7}$ is positive definite for $0<a<1/2$.
   A strict $H_{a,n}$ has nonnegative successor exactly when
   $$
   \int_0^\infty r\sinh(ar)\,
   \mathrm{thetaCuspNativeSuccessorSource}(a,n,r/2)\,dr\ge0.
   $$
   The all-order signed Hankel cone is equivalent to RH.
   See [rank-seven strictness](../RHTower/ThetaCusp/ThetaCuspCenterMixedSeventhRankStrict.lean),
   [native successor](../RHTower/ThetaCusp/ThetaCuspCenterMixedSuccessorSource.lean), and
   [signed-jet completeness](../RHTower/ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness.lean).

5. **Cumulative divisor covariance.** Euler-deletion finite error energy equals
   $$
   \sum_{j,k\le T}c_jc_k
   \left(\frac1{\max(j,k)}-\frac1{T+1}\right).
   $$
   Full energy includes the literal infinite tail.
   See [EulerDeletionAveragedDivisorCovariance](../RHTower/EulerDeletionAveragedDivisorCovariance.lean).

6. **Light channels and their domain boundary.** The reflected Suzuki current plus its
   negative-light Gram equals its positive-light Gram on every finite source and height packet.
   An unrestricted positive extension of the divergent sharp prime source is impossible.
   See [light completion](../RHTower/Suzuki/SuzukiWallFieldLightConeKernelCompletion.lean) and
   [finite-part obstruction](../RHTower/Suzuki/SuzukiCofinalPositiveFinitePartNoGo.lean).

7. **Endpoint precision.** Count has additive stabilizer
   $\mathcal Q=\{\delta:\sum_{n\le x}\delta(n)=O(\sqrt x\log^2x)\}$.
   Complete all-generator tower positivity instead determines every coefficient from $n=2$.
   See [count precision](../ArithmeticOfSquareRootPrecision/PrecisionClassesAndTheCount.lean) and
   [tower rigidity](../ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean).

8. **Gauge variance and census.** Unequal ordered prime pairs have distinct ratios. The twisted
   bandwidth-$4/3$ coalescent source therefore has zero gauge mean and an exact diagonal variance.
   Its normalized variance is at most
   $$(1536/\pi^2)(\log T)^3T^{1+\eta}=o(N(T,2T)^2),\qquad\eta<1.$$
   The actual statistic is its value at the prescribed gauge point zero. Additive prime
   correlations must control that point; the small gauge variance alone does not.
   See [TheCoalescentSurplusIsPureGaugeCharge](../ArithmeticCorrelationGeometry/TheCoalescentSurplusIsPureGaugeCharge.lean).

## Arithmetic Green norm and exact Schur cost

For a period $Q\ge1$, coefficients $a_i$ on $1\le i<Q$, and
$P_a(\zeta)=\sum_i a_i\sum_{r<i}\zeta^r$, define the complete divisor-conductor energy
$$
E_Q(a)=\sum_{m\mid Q,\ m\ne1}\sum_{i,j}a_i a_jG_m(i,j).
$$
Its coefficient reserve has an exact positive remainder:
$$
4E_Q(a)=Q\left[\left(\sum_i a_i\right)^2+\sum_i a_i^2\right]
+\sum_{m\mid Q,\ m\ne1}\sum_{\zeta\ {\rm primitive}\ m}|(1+\zeta)P_a(\zeta)|^2.
$$
Thus the completed arithmetic Gram controls total mass and coefficient square mass simultaneously.
Its interior radical is zero. The proof uses the complementary multiplier $1-\zeta$, whose
Parseval energy is exactly the bracketed coefficient norm.
See [CyclotomicCoercivity](CyclotomicCoercivity.lean), especially
`divisorGramEnergy_completion`, `divisorGramEnergy_coercive`, and
`divisorGramEnergy_eq_zero_iff`.

The same form has a local inverse. Extend an interior coupling $b$ by $b_0=b_Q=0$, and put
$$
(Lb)_i=2b_i-b_{i-1}-b_{i+1},\qquad
D_Q(b)=\sum_{0\le i<Q}(b_{i+1}-b_i)^2.
$$
Then $B_Q^{-1}=L/Q$ on the interior, and
$$
E_Q(a)-2\sum_i a_i b_i+\frac{D_Q(b)}Q
=E_Q\left(a-\frac{Lb}Q\right)\ge0.
$$
Consequently
$$
\max_a\left(2\sum_i a_i b_i-E_Q(a)\right)=\frac{D_Q(b)}Q,
$$
with equality exactly at $a_i=(Lb)_i/Q$ on every interior coordinate.
The two boundary differences belong to the cost. This gives an attained, exact payment for a
mixed coupling in the actual completed arithmetic Gram.
See [DirichletSchurCost](DirichletSchurCost.lean), especially
`bridgePotential_inverse`, `bridgeSchur_completion`, and `bridgeSchurCost_isGreatest`.

Application to a completed Weil block requires identification of its coupling in these coordinates
and an arithmetic bound for this variation energy. The Green inverse alone supplies neither.

## Accumulation, dual variation, and a joint truncation bound

For arbitrary real increments $c_j$, let
$$
C_T(c)=\sum_{1\le n\le T}\frac{(\sum_{j\le n}c_j)^2}{n(n+1)}.
$$
The exact coordinate change $a_j=c_j/j$, $Q=T+1$, gives
$$
E_{T+1}(a)=(T+1)C_T(c),\qquad
4C_T(c)=\left(\sum_{j\le T}\frac{c_j}{j}\right)^2+
\sum_{j\le T}\frac{c_j^2}{j^2}+\frac{R_{T+1}(a)}{T+1}.
$$
Thus accumulation has an explicit coercive norm and a positive cyclotomic remainder.
Its mixed-coupling payment is also local:
$$
2\sum_{j\le T}c_jb_j-C_T(c)\le D_{T+1}(w),\qquad
w_j=jb_j\ (1\le j\le T),\quad w_0=w_{T+1}=0.
$$
Both conductor factors cancel exactly. The cost concerns variation of the weighted coupling,
not its absolute coordinate size.

For the actual Euler-deletion increments at $1\le X<M$, write $F_{X,M}$ for the full
error energy. Its literal coordinate tail obeys the simultaneous estimate
$$
0\le F_{X,M}-C_T(c)\le\frac{(M+1)^2}{T+1}.
$$
This follows from the source bound $|1-\mathrm{modular}(X,M,n)|\le M+1$ and the
telescoping carrier tail. It specifies a horizon large enough for any prescribed truncation
allowance, including when the outer cutoff grows. The estimate does not bound the accumulated
source energy at the inner-cutoff strength required by the Euler-deletion criterion.
See [DivisorCovariance](DivisorCovariance.lean), particularly `cumulativeEnergy_completion`,
`cumulativeEnergy_schur_bound`, and `fullErrorEnergy_truncation_bounds`.

## Arithmetic packets and an actual prime-source estimate

For arbitrary interior arithmetic nodes $k_i$, aggregate colliding coefficients as
$A_r=\sum_{k_i=r}a_i$. The complete packet energy is exactly $E_Q(A)$. Its radical consists
of the packets with every aggregate $A_r=0$. Distinct indices preserve the coefficient square
mass and the quarter reserve. This specifies the precise information retained by arithmetic
compression. See [FinitePackets](FinitePackets.lean).

For a finite prime block $S\subset(P,2P]$, restrict to packets satisfying
$\sum_{p\in S}a_p=\sum_{p\in S}a_p\log p=0$ and put $Q=2P+2$.
Let $\mathcal P_S(a)$ be the actual energy-centered pronic prime-packet form. The complete
first-jump source identity gives $E_Q(A)/Q\le\mathcal P_S(a)$, hence
$$
\sum_{p\in S}a_p^2\le4\mathcal P_S(a),\qquad
2\sum_{p\in S}a_pb(p)-\mathcal P_S(a)\le D_Q(b^0).
$$
Here $b^0$ agrees with $b$ at interior integer coordinates and vanishes at both endpoints.
The estimate retains the actual source's unequal-prime terms and pays an arbitrary coupling
by an explicit variation norm. Its domain constraints are the two stated arithmetic moments.
Identifying a complete Weil remainder with such a coupling remains a separate source problem.
See [PrimePacketSchur](PrimePacketSchur.lean), particularly `divisorGramEnergy_le_primePacket`,
`primePacket_coefficient_reserve`, and `primePacket_schur_bound`.

For $P\ge2$, every prime in the block is odd, and the coefficient reserve improves to
$$\sum_{p\in S}a_p^2\le2\mathcal P_S(a).$$
More generally, distinct nonadjacent integer support has this half reserve in the normalized
completed conductor form. Its zero-boundary coefficient extension has Dirichlet energy
exactly twice its square mass. Applying the Schur bound at half that extension proves the
claim. See [SeparatedPacketReserve](SeparatedPacketReserve.lean), particularly
`packetBridge_separated_reserve` and `primePacket_odd_coefficient_reserve`.

## Exact arithmetic gap geometry

For increasing integer nodes $0=k_0<k_1<\cdots<k_N=Q$, the normalized arithmetic kernel is
$$
K_k(i,j)=\min(k_i,k_j)-\frac{k_i k_j}{Q}.
$$
Its inverse on the interior is the difference of adjacent arithmetic slopes:
$$
(L_kb)_i=\frac{b_i-b_{i-1}}{k_i-k_{i-1}}-
\frac{b_{i+1}-b_i}{k_{i+1}-k_i}.
$$
For $b_0=b_N=0$, write
$$
F_k(a)=\sum_{1\le i,j<N}a_i a_jK_k(i,j),\qquad
D_k(b)=\sum_{0\le i<N}\frac{(b_{i+1}-b_i)^2}{k_{i+1}-k_i}.
$$
Then
$$
F_k(a)-2\sum_i a_i b_i+D_k(b)=F_k(a-L_kb)\ge0,
\qquad
\max_a\left(2\sum_i a_i b_i-F_k(a)\right)=D_k(b).
$$
The maximum is attained at $a=L_kb$. This form is literally $E_Q(A)/Q$ for the
packet supported at the selected nodes, and its interior radical is zero. No interpolation
at omitted integer coordinates enters its inverse or completion cost.

If every gap is at least $\delta>0$, then
$$
D_k(b)\le\frac4\delta\sum_i b_i^2,\qquad
F_k(a)\ge\frac\delta4\sum_i a_i^2.
$$
Both boundary gaps belong to the minimum. Thus arithmetic spacing strengthens the source
reserve through the exact inverse, with reciprocal-gap variation as its dual norm.
See [IrregularGreen](IrregularGreen.lean), particularly `meshGram_eq_completed`,
`meshPotential_inverse`, `meshSchurCost_isGreatest`, and `meshGram_gap_coercive`.

Restriction to these arithmetic nodes has an exact extension theorem:
$$
\min_{u(0)=u(Q)=0,\ u(k_i)=b_i}D_Q(u)=D_k(b).
$$
The minimum is attained by the normalized complete arithmetic potential of $L_kb$.
Its restriction equals $K_kL_kb=b$, and finite Green summation identifies its energy
with $D_k(b)$. The Schur inequality applied to $L_kb$ proves that every competing
extension has at least this cost. Both endpoint gaps enter the minimum.

If the mesh contains a prime block $S\subset(P,2P]$ and $Q=2P+2$, the actual neutral
prime form therefore satisfies
$$
2\sum_{p\in S}a_p b_{i(p)}-\mathcal P_S(a)\le D_k(b),\qquad k_{i(p)}=p.
$$
The source pays prescribed prime couplings by their arithmetic gap energy. Attainment
and minimality concern the conductor comparison; the actual prime form may contain
additional positive energy. See [OptimalInterpolation](OptimalInterpolation.lean),
particularly `meshDirichletEnergy_isLeast_extension` and `primePacket_mesh_schur_bound`.

## Neutral constraints and the exact quotient dual norm

On the same mesh, the mixed Green pairing is
$$
\langle b,c\rangle_D=\sum_{i<N}
\frac{(b_{i+1}-b_i)(c_{i+1}-c_i)}{k_{i+1}-k_i}
=\sum_{0<i<N}b_i(L_kc)_i
$$
for zero endpoint values. Removing a constraint profile $g$ gives the explicit projection
$$
P_gb=b-\frac{\langle b,g\rangle_D}{D_k(g)}g,\qquad
D_k(P_gb)=D_k(b)-\frac{\langle b,g\rangle_D^2}{D_k(g)}.
$$
Division by zero contributes zero: a zero-energy profile vanishes at every selected node.
The projection is therefore defined and orthogonal even for degenerate constraints.
For coefficients satisfying $a\cdot g=0$,
$$
\max_a\{2a\cdot b-F_k(a):a\cdot g=0\}=D_k(P_gb),
$$
attained at $a=L_kP_gb$.

Two constraints have an exact joint payment. Put $v=P_gh$ and $u=P_v(P_gb)$. Then
$$
\max_a\{2a\cdot b-F_k(a):a\cdot g=a\cdot h=0\}
=D_k(u)
=D_k(b)-\frac{\langle b,g\rangle_D^2}{D_k(g)}
-\frac{\langle P_gb,v\rangle_D^2}{D_k(v)}.
$$
The maximizer is $L_ku$; no independence assumption on $g,h$ is needed.
The exact radical is
$$D_k(u)=0\quad\Longleftrightarrow\quad
b_i=\alpha g_i+\beta h_i\quad(0<i<N)
\quad\text{for some }\alpha,\beta\in\mathbb R.$$

For the actual neutral prime source, choose $g_i=1$ and $h_i=\log k_i$ on the interior,
with zero endpoints. Its mass and logarithmic moments annihilate both removed profiles.
Consequently its complete mixed coupling obeys
$$
2\sum_{p\in S}a_pb_{i(p)}-\mathcal P_S(a)\le D_k(u)\le D_k(b).
$$
The attained equality and radical concern the constrained conductor comparison; the actual
prime form retains any additional positive energy. See [NeutralPacketDual](NeutralPacketDual.lean),
particularly `meshDoubleNeutralSchurCost_isGreatest`, `meshDoubleProjection_energy_eq_zero_iff`,
and `primePacket_neutral_mesh_schur_bound`.

## A macroscopic index ceiling for the complete Weil source

For the actual plateau Weil matrix, one prefix horizon $M_0$ has the following property:
whenever $M\ge M_0$, $N\ge M$, $c>0$, and $cM\le N$, every strictly negative subspace
has dimension at most $N-M$. Restriction to tail coordinates is injective on such a
subspace: a nonzero vector supported on the paid prefix would have nonnegative complete energy.

At fixed overlap $c=3/2$ and length $N=3K$, this gives the unconditional eventual bound
$$
\dim W\le K.
$$
The matrix retains its prime, Gamma, polar, and mixed entries. The bound grows with the
horizon; positivity of the remaining Schur form and a finite limiting index remain separate
questions. See [WeilPrefixIndex](WeilPrefixIndex.lean), particularly
`eventually_completeWeil_negative_subspace_dim_le_tail` and
`eventually_three_halves_negative_subspace_dim_le`.

The ceiling extends through the full certified Young range. For every fixed
$1\le d<c_*$, a horizon $M_0(d)$ controls all $M\ge M_0(d)$, $N\ge M$, and $c>0$
with $cM=dN$: every strictly negative subspace has dimension at most $N-M$.
Here $c_*>1$ is the unique zero of the optimized complete Young floor. The exact
principal-prefix identity identifies the paid block with the complete length-$M$
source at overlap $d$. Its remaining dimension fraction is $1-d/c$.
See `eventually_completeWeil_negative_subspace_dim_le_young_tail` and
[TransMetzlerYoungOptimization](../TransMetzlerWeilPositivity/TransMetzlerYoungOptimization.lean).
The certificate boundary describes this proved positive range; it does not assert
that the actual matrix is indefinite beyond that range.

## Exact native-tail reserves and their rank boundary

Write $(r)_n=\prod_{j<n}(r+j)$. The scaled Gamma moments $m_k=gw^k(r)_k$, with
$g,w,r>0$, have exact determinant and successor reserve
$$
\det[m_{i+j}]_{i,j<N}=\prod_{j<N}gw^{2j}j!(r)_j,\qquad
S_N(m)=gw^{2N}N!(r)_N.
$$
The determinant follows from monic factorial evaluation at consecutive nodes. Its successive
quotient retains the complete mixed row. See [GammaSuccessorReserve](GammaSuccessorReserve.lean).

For the complete native reflection jet $R_n(x)$, first-atom mass $f_1(x)$, and actual scale
$q(x)=\pi e^{2x}$, use the balanced moments
$$
\sigma_{s,k}(x)=\frac{(-1)^{s+k}R_{2(s+k)}(x)}{f_1(x)^2q(x)^{s+k}}.
$$
At every fixed rank $N$ and shift $s$, the limiting Gamma parameters are
$g=16^s(\tfrac12)_s$, $w=16$, $r=s+\tfrac12$. If $A_{N,s}(x)$ is the balanced native
head and $G_{N,s}$ this Gamma head, both
$$
A_{N,s}(x)-\tfrac12G_{N,s},\qquad \tfrac32G_{N,s}-A_{N,s}(x)
$$
are positive definite on a cofinal ray. Thus the comparison controls every vector in the
fixed head in its full Gamma quadratic norm. Its successor satisfies
$$
S_N(\sigma_s(x))\longrightarrow
C_{N,s}=16^{s+2N}(\tfrac12)_sN!(s+\tfrac12)_N>0,
$$
and eventually lies between $C_{N,s}/2$ and $3C_{N,s}/2$. The literal infinite theta
remainder enters the proved entrywise limit; no source truncation occurs.

Absolute reserve growth conceals a relative loss:
$$
\frac{S_N(\sigma_s(x))}{\sigma_{s,2N}(x)}
\longrightarrow\frac{N!}{(s+\tfrac12+N)_N}\le(\tfrac23)^N.
$$
For every $\delta>0$, some finite rank has actual native ratio below $\delta$ on a cofinal
ray. Therefore no positive diagonal-relative reserve works for all ranks, even if each
rank chooses its own threshold. The surviving comparison uses the full Gamma norm and
the exact rank-dependent successor constant. Compact-source compensation and simultaneous
rank exhaustion remain separate questions.
See [NativeTailReserve](NativeTailReserve.lean), particularly
`nativeBalancedHead_relative_posDef_eventually`, `nativeBalancedSuccessor_tendsto`, and
`not_native_rank_uniform_relative_reserve`.

The full signed heads retain both parity sectors exactly. For
$s(2k)=m_k$, $s(2k+1)=0$, simultaneous row and column permutation gives
$$
H_N(s)\cong H_{\lceil N/2\rceil}(m)\oplus
H_{\lfloor N/2\rfloor}(m_{\cdot+1}).
$$
Positive definiteness and semidefiniteness are equivalent to the corresponding properties
of both blocks; the full determinant is their product. Applying this identity to the literal
complete native signed jets proves that every fixed full head is positive definite on its
own cofinal ray. All odd entries are the source's exact zeros. The result retains arbitrary
mixed entries within each parity sector and makes no claim of a common horizon for all ranks.
See [SignedParityTransfer](SignedParityTransfer.lean), particularly
`finiteHankelMatrix_parity`, `finiteHankelMatrix_evenMomentSequence_posSemidef_iff`, and
`nativeSignedHead_posDef_eventually`.

## An escaping obstruction in the literal first atom

At every real center $x$, the first theta atom has a negative signed reflection moment:
$$
\exists k,\qquad m_k^{(1)}(x)=
(-1)^k\partial_t^{2k}[f_1(x+t)f_1(x-t)]_{t=0}<0.
$$
Consequently some finite full signed Hankel section has a negative diagonal. No source
horizon makes all first-atom signed moments nonnegative.

This follows from the exact source profile, without a numerical rank witness. Set
$q=\pi e^{2x}$, $B=(2q-3)^2$, and $C=4q^2e^{x-2q}>0$. Its entire continuation at $t=iy$ is
$$
g_x(y)=Ce^{-2q(\cos(2y)-1)}[B-12q(\cos(2y)-1)].
$$
Nonnegative signed moments would make every real Taylor coefficient of $g_x$ nonnegative,
hence make $g_x$ nondecreasing on $[0,\infty)$. The literal values contradict this:
$$g_x(\pi/2)=Ce^{4q}(B+24q)>CB=g_x(\pi).$$

The positive survivor determines a source-dependent order invariant:
$$\nu(x)=\min\{k:m_k^{(1)}(x)<0\}<\infty,\qquad \nu(x)\longrightarrow\infty.
$$
Every fixed shifted balanced first-atom Hankel head is positive definite on its own cofinal
ray. Each fixed raw signed moment is eventually positive, so a finite intersection pushes
$\nu(x)$ beyond every prescribed order. The invariant records the first negative moment;
mixed entries may obstruct positivity of a Hankel head before that diagonal appears.

The complete mixed boundary has its own finite invariant:
$$
\kappa(x)=\min\{N:H_N(s_x^{(1)})\text{ is not positive semidefinite}\},\qquad
\kappa(x)\le\nu(x)+1,\qquad \kappa(x)\longrightarrow\infty.
$$
Every smaller head is positive semidefinite at that same center. Positive mass and scale
congruences transfer the balanced shifted estimates to the literal first-atom moments;
the exact parity identity then makes every fixed full signed head eventually positive
definite. A finite intersection pushes its first failing dimension beyond any fixed bound.
Thus the escaping obstruction concerns the whole mixed form as well as individual moments.

Its physical scale has an effective ceiling. Put $H=e^{4\pi}$. At every real center,
$$
2^{2\nu(x)}\le
\frac{e^{2q(H+1)}[(2q-3)^2+12q(H+1)]}{6q}.
$$
For $x\ge0$, this gives the explicit bounds
$$
\nu(x)\le C_*q(x),\qquad \kappa(x)\le1+C_*q(x),\qquad
C_*=\frac{9e^{4\pi}+2}{2\log2}.
$$
The constant is coarse. The proof bounds the entire rotated source on $|z|=2\pi$,
then uses Cauchy's coefficient estimate to bound its Taylor tail. If all derivatives
below order $2\nu(x)$ are nonnegative, its Taylor head cannot decrease between
$\pi/2$ and $\pi$. The two tails must therefore pay the actual decrease of at least
$24qC$. This forces the displayed finite rank window without a numerical witness.
See [FirstAtomEffectiveRankBoundary](FirstAtomEffectiveRankBoundary.lean), particularly
`firstAtomNegativeOrder_pow_bound`, `firstAtomNegativeOrder_le_physicalScale`, and
`exists_firstAtom_signed_head_failure_le_scale`.

The complete theta source has a different analytic domain. Its original complex atom series
is summable exactly when $\cos(2\operatorname{Im}z)>0$. The periodic entire argument above
therefore cannot be applied to that complete series across its nonsummable sectors.
See [FirstAtomRankBoundary](FirstAtomRankBoundary.lean), particularly
`exists_firstAtom_signed_moment_neg`, `exists_firstAtom_signed_head_not_posSemidef`,
`firstAtomSignedHead_posDef_eventually`, `firstAtomNegativeOrder_tendsto`, and
`firstAtomFailureRank_tendsto`;
the exact complete-source admission theorem is
[ThetaCuspComplexClockSector](../RHTower/ThetaCusp/ThetaCuspComplexClockSector.lean).

## Explicit rank and center comparisons

The normalized first atom admits a simultaneous analytic estimate. Put
$$
\gamma_k=16^k(\tfrac12)_k=\frac{4^k(2k)!}{k!},\qquad
D=e^{4+2e^2}(24+10e^2).
$$
At $q\ge3$, its rotated profile in the coordinates $z/\sqrt q$ differs from
$e^{4z^2}$ by at most $D/q$ on the complex unit disk. The quartic remainder of
$\cosh$ controls the exponential factor and the exact affine source factor.
Cauchy's estimate gives every signed first-atom moment the bound
$$
|\sigma_k^{(1)}(x)-\gamma_k|\le\frac{(2k)!D}{q(x)}.
$$
Consequently $q(x)>D K!$ implies $K<\nu(x)$. A sufficient center is
$\max(0,\tfrac12\log((D K!+1)/\pi))$.
See [FirstAtomGaussianHorizon](FirstAtomGaussianHorizon.lean), especially
`firstAtomScaledEvenJet_gaussian_error_le` and `firstAtomNegativeOrder_gt_of_horizon`.

Mixed heads require the inverse of the full comparison. For any real positive definite
$N\times N$ matrix $G$,
$$
v_i^2\le (G^{-1})_{ii}\,v^TGv,\qquad
\|v\|_2^2\le\operatorname{tr}(G^{-1})\,v^TGv.
$$
Thus an entrywise error $|A_{ij}-G_{ij}|\le\epsilon$ has relative form cost
$N\epsilon\operatorname{tr}(G^{-1})$. A cost below $1/2$ leaves the strict reserve
$A-G/2>0$. See [InverseTraceStability](InverseTraceStability.lean).

For $G_{N,s}=[\gamma_{i+j+s}]_{i,j<N}$, write $T_{N,s}=\operatorname{tr}(G_{N,s}^{-1})$.
This is a finite cofactor sum divided by the exact positive Gamma determinant.
The first-atom shifted head has relative error at most
$$\frac{N T_{N,s}(2(s+2N))!D}{q(x)}.$$
Let $E=\lceil R/2\rceil$, $O=\lfloor R/2\rfloor$. Both parity sectors are strictly positive if
$$
q(x)\ge Q_R^{(1)}=3+2D\big[E T_{E,0}(4E)!+O T_{O,1}(2+4O)!\big].
$$
This gives $R<\kappa(x)$, an explicit lower boundary for the whole mixed first-atom form.
See [FirstAtomMixedHorizon](FirstAtomMixedHorizon.lean), particularly
`gaussianInverseTrace_eq_cofactor_div`, `firstAtomBalancedHead_relative_error_le`, and
`firstAtomFailureRank_gt_of_horizon`.

The infinite theta remainder also has a simultaneous payment. Its literal estimate is
$|\sigma_k-\sigma_k^{(1)}|\le27\,24^{2k}q^k(e^{3\pi}/399)e^{-3q}$ at $q\ge2k+6$.
The exponential series bounds $q^{L+1}e^{-q}$ by $(L+1)!$, so for all $k\le L$ and
$q\ge2L+6$,
$$
|\sigma_k(x)-\gamma_k|\le\frac{C_L}{q(x)},\qquad
C_L=(2L)!D+27\,24^{2L}\frac{e^{3\pi}}{399}(L+1)!.
$$
The complete shifted head therefore has relative cost $N T_{N,s}C_{s+2N}/q$.
For the full signed rank $R$, the explicit scale
$$
Q_R^{\mathrm{nat}}=2(R+1)+6+
2\big[E T_{E,0}C_{2E}+O T_{O,1}C_{1+2O}\big]
$$
pays both analytic domains and both mixed parity sectors:
$$q(x)\ge Q_R^{\mathrm{nat}}\quad\Longrightarrow\quad H_R(s_x^{\mathrm{nat}})>0.$$
Thus $x\ge\max(0,\tfrac12\log(Q_R^{\mathrm{nat}}/\pi))$ is a sufficient joint
rank–center condition. All constants are explicit finite expressions. The complete source
and all its mixed entries remain present. See [NativeGaussianHorizon](NativeGaussianHorizon.lean),
especially `nativeBalancedHead_relative_error_le` and `nativeSignedHead_posDef_of_horizon`.

These bounds are coarse. They give no common source center for all ranks and do not pay the
compact-center contribution in the RH-equivalent integrated signed hierarchy.

## Relative control of exact successor costs

Ordering complete successor forms orders their Schur reserves. If the preceding heads
of $m$ and $g$ are strict and $H_{N+1}(m)\ge H_{N+1}(g)$, then
$S_N(m)\ge S_N(g)$, even when either successor reserve is negative. Subtract
$S_N(g)$ from the terminal moment $2N$. The adjusted $g$ head lies exactly on
its semidefinite boundary, and the same adjustment to $m$ remains semidefinite.
The preceding heads and mixed rows are unchanged.

Consequently a relative comparison in the full $(N+1)$-dimensional form gives
$$
|v^T(H_{N+1}(m)-H_{N+1}(g))v|\le\eta\,v^TH_{N+1}(g)v,
\quad H_{N+1}(g)>0,\quad 0\le\eta<1
$$
$$\Longrightarrow\quad |S_N(m)-S_N(g)|\le\eta S_N(g).$$
No additional inverse perturbation factor occurs. See
[SuccessorComparison](SuccessorComparison.lean), particularly
`successorSchur_mono` and `successorSchur_relative_error`.

For the complete native source put $M=N+1$, $L=s+2M$, and
$$A_{N,s}=M T_{M,s}C_L,\qquad \eta_{N,s}(x)=A_{N,s}/q(x).$$
At $q\ge2L+6$ and $q>A_{N,s}$,
$$
|S_N(\sigma_s(x))-C_{N,s}|\le\frac{A_{N,s}}q C_{N,s}.
$$
The explicit scale $Q_{N,s}=2L+6+2A_{N,s}$ therefore gives
$$q(x)\ge Q_{N,s}\quad\Longrightarrow\quad
\tfrac12C_{N,s}<S_N(\sigma_s(x))<\tfrac32C_{N,s}.$$
The sufficient source center is $\max(0,\tfrac12\log(Q_{N,s}/\pi))$.
These bounds retain every native mixed entry and the infinite theta remainder.
See [NativeSuccessorHorizon](NativeSuccessorHorizon.lean), especially
`nativeBalancedSuccessor_relative_error_le` and
`nativeBalancedSuccessor_half_bounds_of_horizon`.

## Strict seam geometry and two complete-source regions

Let $\Phi$ be the complete theta source, $h_k$ its native signed reflection jet,
and $U_k(r)=\int_{s>r}h_k(s/2)\,ds$. The seam matrix $S_N=[U_{i+j}(0)]$ satisfies
$$v^\mathsf TS_Nv=\int_{\mathbb R}\left|\sum_{j<N}v_j(2i)^j\Phi^{(j)}(x)\right|^2dx.$$
Every finite derivative family of $\Phi$ is linearly independent. Integration against
$x^k$ recovers its coefficients through a triangular system with nonzero diagonal
$(-1)^k k!\int\Phi$. Thus $S_N$ is positive definite at every rank: the seam has
zero radical, including for complex derivative packets.

Write $K_k=$ `thetaCuspNativeJetDecayConstant k`, $D_N=\sum_{k\le2N}K_k$, and
$A_N=N D_N\operatorname{tr}(S_N^{-1})$. The literal tail difference obeys
$$|U_k(r)-U_k(0)|\le rK_k,\qquad
|v^\mathsf T(H_N(U(r))-S_N)v|\le rA_Nv^\mathsf TS_Nv.$$
Consequently
$$0\le r\le[2(1+A_N)]^{-1}\quad\Longrightarrow\quad H_N(U(r))-\tfrac12S_N>0.$$
At the other end, $r\ge2\,\mathrm{nativeMixedHorizon}(N)$ implies $H_N(U(r))>0$:
its quadratic form is the integral of strictly positive complete native forms.
Both regions retain all theta atoms and all mixed entries. The intervening compact
interval is the remaining tail-compensation region; these estimates do not assert
positivity throughout it or uniformly over rank.

See [SeamCoercivity](SeamCoercivity.lean), particularly
`thetaDerivativePacket_coefficients_eq_zero`, `nativeTailHead_zero_posDef`,
`nativeTailHead_half_posDef_of_seam_radius`, and `nativeTailHead_posDef_of_horizon`.

## An exact positive clock and its transport boundary

The first atom has an exact all-order comparison beyond its Gaussian limit. With
$q=\pi e^{2x}$, $B=(2q-3)^2$, and $C=4q^2e^{x-2q}$, the invertible real coordinate
$u=\operatorname{arsinh}(t/\sqrt q)$ gives the literal identity
$$
\rho_x(t)=f_1(x+u)f_1(x-u)=Ce^{-4t^2}(B-24t^2),\qquad
f_1(x+u)f_1(x-u)=\rho_x(\sqrt q\sinh u).
$$
Its signed moments and shifted heads are exactly
$$
(-1)^k\rho_x^{(2k)}(0)
=C\big[(B-3)\gamma_k+\tfrac38\gamma_{k+1}\big]
=C\gamma_k(B+6k),
$$
$$H_{N,s}(\rho_x)=C\big[(B-3)G_{N,s}+\tfrac38G_{N,s+1}\big].$$
For $B\ge3$, all shifted heads and all full signed heads are positive definite
simultaneously at the same center. This includes every $x\ge0$.

At those same centers, the physical-coordinate first atom has its finite failing
rank $\kappa(x)$. Thus an exact invertible nonlinear source coordinate can turn
an indefinite all-order hierarchy into a positive Gamma mixture. Positivity of
the clocked form supplies no positivity of its physical pullback. The comparison
is exact; the missing transfer concerns the nonlinear derivative transformation.
See [HyperbolicClock](HyperbolicClock.lean), especially
`firstAtomGaussianClockProfile_eq`, `firstAtomGaussianClockProfile_signed_even_jet`,
and `firstAtomGaussianClock_positive_pullback_fails`.

The coefficient boundary is exact. For arbitrary real $a,b$, interleave the moments
$a\gamma_k+b\gamma_{k+1}$ with odd zeros. Every finite full head is positive semidefinite
if and only if $a,b\ge0$; every finite head is strict if and only if also $a+b>0$.
The Gaussian density
$$J_{a,b}(y)=(a+by^2)e^{-y^2/32},\qquad d\mu=e^{-y^2/32}\,dy,$$
has precisely these moments up to one positive common mass. Polynomial test closure
identifies the entire Hankel cone with $J_{a,b}\ge0$, which forces both coefficients
to be nonnegative.

For the actual clock, $a=B-3$ and $b=3/8$. Thus $B\ge3$ is necessary and sufficient
for all-rank positivity and strictness. At $B<3$, every signed even moment
$C\gamma_k(B+6k)$ remains nonnegative, but some finite mixed head fails.
Individual moment signs do not determine the complete cone even in this explicit
Gaussian source coordinate. See [GaussianClockCone](GaussianClockCone.lean),
`affineGamma_all_head_posSemidef_iff`, `affineGamma_all_head_posDef_iff`,
and `firstAtomGaussianClock_mixed_failure_of_shape_lt_three`.

The physical clock also has an exact all-order transport operator. For
$g(q,t)=\exp[-2q(\cosh(2t)-1)]$ and $H_k(q)=(-1)^k\partial_t^{2k}g(q,0)$,
$$H_0=1,\qquad H_{k+1}=8qH_k+(16q^2-4q)H'_k-4q^2H''_k.$$
The actual first-atom signed moment is exactly
$$(-1)^k\partial_t^{2k}[f_1(x+t)f_1(x-t)]_{t=0}
=C[BH_k(q)+6qH'_k(q)].$$
Joint smoothness discharges the scale–reflection derivative commutations at every
order. The negative second-derivative term remains part of the physical transport.
See [ScaleJetTransport](ScaleJetTransport.lean), `gaussianScaleSignedJet_succ`
and `firstAtomSignedMoment_eq_scaleJet`.

This transport has an exact positive coefficient envelope. Set $\mathcal E=X\partial_X$ and
$$P_0=1,\qquad P_{k+1}=8XP_k+16X\mathcal EP_k+4\mathcal E^2P_k.$$
Every coefficient of $P_k$ is nonnegative, its degree is at most $k$, and its leading
coefficient is $\gamma_k$. The physical identity is $H_k(q)=(-1)^kP_k(-q)$.
The complete affine envelope is $BP_k+6\mathcal EP_k$, with leading coefficient
$(B+6k)\gamma_k$. Removing that coefficient leaves a nonnegative polynomial, so
reflection gives the exact source estimate
$$\left|(-1)^k\partial_t^{2k}[f_1(x+t)f_1(x-t)]_{t=0}
-C(B+6k)\gamma_kq^k\right|
\le C(B+6k)[P_k(q)-\gamma_kq^k].$$
All lower-degree clock losses are retained in this bound.
See [GaussianScalePolynomial](GaussianScalePolynomial.lean),
`gaussianScaleSignedJet_eq_polynomial` and `firstAtomSignedMoment_polynomial_error_le`.

The envelope has the quantitative bound
$$[8q-k(k-1)]P_k(q)\le8q\gamma_kq^k,\qquad q>0,\quad q\ge k^2.$$
Indeed, $\mathcal EP_k\le kP_k$ and $\mathcal E^2P_k\le k^2P_k$ on the positive
ray. The induction closes through the exact nonnegative difference
$$8q(2k+1)[8q-k(k-1)]
-[8q(2k+1)+4k^2][8q-k(k+1)]=16qk+4k^3(k+1).$$
Thus $7P_k(q)\le8\gamma_kq^k$ and
$7q[P_k(q)-\gamma_kq^k]\le k^2\gamma_kq^k$. At $q\ge\max(3,K^2)$, every $k\le K$ obeys
$$(-1)^k\partial_t^{2k}[f_1(x+t)f_1(x-t)]_{t=0}
\ge\tfrac67 C(B+6k)\gamma_kq^k>0.$$
Consequently $K<\nu(x)$ and, whenever $q\ge3$, $\sqrt q<\nu(x)$.
A sufficient center for $K<\nu(x)$ is $\max(0,\tfrac12\log((3+K^2)/\pi))$.
In the original mass normalization, the same source estimate gives
$$|\sigma_k^{(1)}-\gamma_k(1+6k/B)|
\le(1+6k/B)\frac{k^2\gamma_k}{7q},\qquad
|\sigma_k^{(1)}-\gamma_k|\le\frac{3k^2\gamma_k}{q}.$$
These are simultaneous order–center bounds for the physical source; individual moment
positivity does not imply mixed-head positivity.
See [FirstAtomPolynomialHorizon](FirstAtomPolynomialHorizon.lean),
`firstAtom_signed_moment_six_sevenths_le`, `sqrt_scale_lt_firstAtomNegativeOrder`,
and `firstAtomScaledEvenJet_quadratic_error_le`.

Relative mixed-entry errors admit a variance-sensitive payment. For a positive
definite comparison $G$ define
$$V(G)=\sum_iG_{ii}(G^{-1})_{ii}
=\frac{\sum_iG_{ii}\operatorname{adj}(G)_{ii}}{\det G},\qquad V(G)\ge N.$$
Positivity gives $|G_{ij}|\le\sqrt{G_{ii}G_{jj}}$. Therefore
$$|A_{ij}-G_{ij}|\le\epsilon|G_{ij}|
\quad\Longrightarrow\quad
|v^\mathsf T(A-G)v|\le N\epsilon V(G)\,v^\mathsf TGv.$$
Each variance multiplies its own exact inverse-coordinate cost. The proof first
normalizes the entry bound by $\sqrt{G_{ii}G_{jj}}$, then applies the inverse
evaluation inequality to the weighted square mass. Every mixed entry remains present.
See [WeightedInverseStability](WeightedInverseStability.lean),
`relative_entry_error_le_varianceInverseCost` and `varianceInverseCost_eq_cofactor_div`.

The complete theta source has the corresponding relative moment estimate. Put
$A=27e^{3\pi}/399$ and $Q_L=\max(L^2,8L,2L+6)$. For every $k\le L$,
$$q\ge Q_L\quad\Longrightarrow\quad
|\sigma_k(x)-\gamma_k|\le\frac{(3L^2+A)\gamma_k}{q}.$$
The literal infinite remainder costs at most $A\gamma_k/q$ at
$q\ge\max(8k,2k+6)$: $q^ke^{-q}\le k!$ and $8^kk!\le\gamma_k$
pay its power and factorial, while $72^k\le e^{8k}$ pays the remaining order
factor against the source exponential. This estimate includes every theta atom.
See [NativePolynomialHorizon](NativePolynomialHorizon.lean),
`nativeScaledEvenJet_firstAtom_relative_error_le` and
`nativeScaledEvenJet_quadratic_relative_error_le_through`.

For $G_{N,s}=[\gamma_{i+j+s}]$, put $V_{N,s}=V(G_{N,s})$ and
$$L=s+2N,\qquad B_{N,s}=N V_{N,s}(3L^2+A).$$
The complete native head satisfies
$$q\ge Q_L\quad\Longrightarrow\quad
|v^\mathsf T(H_N(\sigma_s(x))-G_{N,s})v|
\le\frac{B_{N,s}}q v^\mathsf TG_{N,s}v.$$
If also $q>2B_{N,s}$, the difference $H_N(\sigma_s(x))-G_{N,s}/2$ is positive
definite. The exact native successor has the same relative payment at dimension $N+1$:
$$|S_N(\sigma_s(x))-C_{N,s}|\le\frac{B_{N+1,s}}q C_{N,s},
\qquad q\ge Q_{s+2(N+1)},\quad q>B_{N+1,s}.$$
Consequently $q\ge Q_{s+2(N+1)}+2B_{N+1,s}$ gives
$C_{N,s}/2<S_N(\sigma_s(x))<3C_{N,s}/2$.
The corresponding center is the positive part of half the logarithm of this scale divided by $\pi$.
The variance cost is an explicit weighted cofactor sum over the exact Gamma determinant.
Its rank dependence remains present; a polynomial moment-order estimate alone does not
establish a polynomial mixed-rank horizon.
See [NativeVarianceHorizon](NativeVarianceHorizon.lean),
`nativeBalancedHead_polynomial_relative_error_le`,
`nativeBalancedHead_half_posDef_of_polynomial_scale`, and
`nativeBalancedSuccessor_half_bounds_of_polynomial_horizon`.

## The relative source in Gaussian polynomial coordinates

Let $F_q$ be the mass-normalized first-atom source at Gaussian length scale and set
$$K_q(z,w)=e^{-4z^2-4w^2}F_q(z+w),\qquad D=50e\exp(2e).$$
For $R\ge1$, $q\ge\max(3,4R^2,R^4)$, and $|z+w|\le R$, the exact source satisfies
$$|K_q(z,w)-e^{8zw}|\le D\frac{R^4}{q}e^{8|z||w|}.$$
Indeed, for $u=2i(z+w)/\sqrt q$, $\delta=\cosh u-1$, and $B=(2q-3)^2$,
$$K_q(z,w)=e^{8zw}e^E(1-12q\delta/B),\qquad
E=-2q(\cosh u-1-u^2/2).$$
The source bounds are $|E|\le2eR^4/q\le2e$ and $|12q\delta/B|\le48eR^4/q$.
The factor $e^{8zw}$ remains intact before taking absolute values. This preserves
the cancellation needed to compare Hermite coefficients without separate Gaussian
growth penalties in the two variables. The estimate concerns the literal first atom;
a mixed-rank theorem also requires the coefficient payment and the infinite remainder.

See [GaussianRelativeKernel](GaussianRelativeKernel.lean), particularly
`gaussianRelativeProfile_error_le` and `firstAtomWickKernel_error_le`.

For positive radii $r,s$ with $r+s\le R$, the mixed error jet has the bound
$$|\partial_z^i\partial_w^j(K_q-e^{8zw})(0,0)|
\le\frac{i!j!}{r^is^j}\,D\frac{R^4}{q}e^{8rs}.$$
The comparison jet is exactly $\mathbf1_{i=j}8^ii!$. The proof differentiates
the first coordinate on the joint analytic domain before applying the second
Cauchy estimate; no interchange of an uncontrolled limiting derivative is required.
See [WickCauchyPayment](WickCauchyPayment.lean),
`firstAtomWickError_mixed_jet_le` and `mixedKernelJet_gaussian`.

The exact contraction formula for any entire $h$ is
$$\partial_z^i\partial_w^j(e^{8zw}h(z+w))_{(0,0)}
=\sum_{r\le\min(i,j)}\binom ir\binom jr8^rr!\,h^{(i+j-2r)}(0).$$
For $h(z)=e^{-4z^2}F_q(z)-1$, its left side is the literal physical Hermite
error jet. A single source-relative Cauchy contour bounds the remaining
one-variable derivative. See [GaussianJetConvolution](GaussianJetConvolution.lean),
`mixedKernelJet_gaussianMultiplier` and `gaussianProfileError_jet_le`.

The adaptive radii and weights
$$r_n=\sqrt{(n+1)/8},\qquad w_n=\sqrt{n!/(n+1)^n}$$
obey the exact normalization
$$\frac{n!}{r_n^n}=w_n\sqrt{8^nn!}.$$
For $i,j\le N$,
$$w_iw_je^{8r_ir_j}\le e^2(N+1),\qquad r_i+r_j\le\sqrt{N+2}.$$
Stirling's bound supplies $w_n^2\le e(n+1)e^{-n}$; the inequality
$16r_ir_j\le i+j+2$ cancels the exponential degree cost. These estimates include
zero degree. See [HermiteRadiusPayment](HermiteRadiusPayment.lean), particularly
`hermiteContourPairWeight_le` and `hermiteContour_factorial_identity`.

The coordinate matrix is literal:
$$T_{nk}=\binom nk\left.\frac{d^{n-k}}{dt^{n-k}}e^{-4t^2}\right|_{t=0}.$$
It is lower triangular with diagonal one, determinant one, and bijective transpose
action at every finite rank. For any entire source $F$, its complete real mixed
kernel head satisfies
$$[\Re\partial_z^i\partial_w^j(e^{-4z^2-4w^2}F(z+w))_{(0,0)}]
=T_N[\Re F^{(i+j)}(0)]T_N^{\mathsf T}.$$
For $F(z)=e^{4z^2}$ the result is exactly $\operatorname{diag}(8^ii!)$.
The coefficient envelope $|T_{nk}|\le n!e^4$ controls the cost of transporting
an exponentially small source remainder. See [HermiteJetCongruence](HermiteJetCongruence.lean),
`realWickJetMatrix_eq_congruence` and `hermiteJetCoefficient_abs_le`.

Put $C_N=De^2(N+1)(N+2)^2$ and $\mathcal D_N=\operatorname{diag}(8^ii!)$.
On $q\ge4(N+2)^2$, every mixed source entry through degrees $i,j\le N$ satisfies
$$|\partial_z^i\partial_w^j(K_q-e^{8zw})(0,0)|
\le\frac{C_N}{q}\sqrt{8^ii!}\sqrt{8^jj!}.$$
Consequently the complete rank-$N$ first-atom Hermite head obeys
$$|v^{\mathsf T}(H^{(1)}_{\rm Hermite}-\mathcal D_N)v|
\le\frac{NC_N}{q}v^{\mathsf T}\mathcal D_Nv.$$
This quartic rank payment follows from the actual source and retains every mixed
coefficient. See [HermiteSourceBound](HermiteSourceBound.lean),
`firstAtomWickError_normalized_jet_le` and `firstAtomHermiteHead_relative_error_le`.

The complete native moment remainder obeys
$|\sigma_k^{\rm native}-\sigma_k^{(1)}|\le A24^{2k}q^ke^{-3q}$,
$A=27e^{3\pi}/399$, on $q\ge2k+6$.
Transporting both finite coefficient sums gives
$$|(H^{\rm native}_{\rm Hermite}-H^{(1)}_{\rm Hermite})_{ij}|
\le N^2(N!)^2e^8 A24^{2N}q^Ne^{-3q}.$$
For $q\ge16(N+2)^2$ this is at most $Ae^8/q$. The exponential source decay
pays the factorial transformation before a reciprocal-scale bound is taken.
The estimate retains the full infinite theta remainder. See
[HermiteNativeTail](HermiteNativeTail.lean), `nativeHermiteHead_firstAtom_raw_error_le`
and `nativeHermiteHead_firstAtom_error_le`.

Let $\mathcal G_N$ be the full signed Gaussian moment head and $H_N^{\rm native}$
the complete native head in the same mass and length coordinates. Define
$$P_N=N\bigl(De^2(N+1)(N+2)^2+Ae^8\bigr).$$
For $q\ge16(N+2)^2$,
$$|v^{\mathsf T}(H_N^{\rm native}-\mathcal G_N)v|
\le\frac{P_N}{q}v^{\mathsf T}\mathcal G_Nv.$$
The Hermite diagonal norms are at least one, so the native remainder fits the
same weighted entry bound as the first atom. Bijectivity of $T_N^{\mathsf T}$
returns the resulting estimate to every original source direction with no inverse
cost. If also $q>2P_N$, then $H_N^{\rm native}-\mathcal G_N/2$ is positive definite.
Thus the complete source has a polynomial mixed-rank scale. See
[NativeHermiteHorizon](NativeHermiteHorizon.lean),
`nativeBalancedFullHead_polynomial_rank_error_le` and
`nativeBalancedFullHead_half_posDef_of_polynomial_rank_scale`.

The monomial embedding $i\mapsto2i+s$ identifies the shifted rank-$n$ even-moment
head with a principal restriction of full signed dimension $M=2n+s$.
Its complete relative error is therefore $P_M/q$, on $q\ge16(M+2)^2$.
For the exact rank-$n$ successor, use $M=2(n+1)+s$:
$$|S_n(\sigma_s^{\rm native}(x))-C_{n,s}|
\le\frac{P_M}{q}C_{n,s},\qquad q\ge16(M+2)^2,\quad q>P_M.$$
Define
$$S_M=16(M+2)^2+2P_M,\qquad X_M=\max(0,\tfrac12\log(S_M/\pi)).$$
Then $x\ge X_{2(n+1)+s}$ gives
$C_{n,s}/2<S_n(\sigma_s^{\rm native}(x))<3C_{n,s}/2$.
The exact Schur comparison preserves the relative error without another
conditioning factor. See [PolynomialRankHorizon](PolynomialRankHorizon.lean),
`nativeBalancedHead_polynomial_rank_error_le`,
`nativeBalancedSuccessor_polynomial_rank_error_le`, and
`nativeBalancedSuccessor_half_bounds_of_polynomial_rank_horizon`.

The physical shifted head is exactly
$$H^{\rm physical}_{n,s}(x)=q^sD\,H_n(\sigma_s^{\rm native}(x))D,
\qquad D_{ii}=\theta_1(x)q^i.$$
On the stated scale, $q>0$ and $\theta_1(x)\ne0$, so this congruence preserves
strictness. Both parity blocks of the literal full signed rank-$N$ source fit in
dimension $M=N+1$; $q\ge S_{N+1}$ therefore makes that full physical head positive definite.
With the universal constant
$$C=16+2De^2+2Ae^8,$$
the explicit scale satisfies $S_M\le C(M+2)^4$.
Thus the complete physical signed rank-$N$ head is strict whenever
$$x\ge\max\left(0,\tfrac12\log(C/\pi)+2\log(N+3)\right).$$
The identical logarithmic envelope at $M=2(n+1)+s$ pays the exact native successor.
See [NativePhysicalRankHorizon](NativePhysicalRankHorizon.lean),
`nativeSignedHead_posDef_of_logarithmic_rank_horizon` and
`nativeBalancedSuccessor_half_bounds_of_logarithmic_rank_horizon`.

## Place in the research

| Programme | Connection |
|---|---|
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Complete Weil geometry, orientation, and index |
| CriticalArithmeticCorrelationTheory | Arithmetic Grams, radicals, residue averaging |
| ArithmeticCorrelationGeometry | Gauge variance, additive correlations, and actual source evaluation |
| TransMetzlerWeilPositivity | Complete positive overlap range and profile-dependent exhaustion |
| ArithmeticIndexDescent | Joint Gamma, prime-power, polar, coarse, and detail reserves |
| EffectiveArithmeticHodgeTheory, HeckeKreinToeplitz | Height localization and orbit-kernel classification |
| ConjugateDiagonalGeometry | Positive depth metric and moving theta reconstruction |
| ArithmeticOfSquareRootPrecision | Error classes for counting and exact-source positivity |
| TransThresholdPairCorrelation | Signed coalescent functional and census thresholds |
| ThetaCusp, Suzuki, CCM, Li clock modules | Actual analytic and causal source forms |

The height Hasse theorem and orbit-kernel converse Krein–Langer theorem are established inputs.
A source-side upper index bound is a different theorem. Sharing an RH endpoint does not establish
a norm-preserving transfer between programmes.

## Research questions

1. **Signed theta successors.** Can native compensation propagate rank-seven strictness to arbitrary
   rank? The first explicit residual is the order-seven successor integral. Degenerating reserves
   require quantitative bounds or controlled radicals. The complete native tail has an exact
   Gamma reserve, but its fraction of the next diagonal decreases exponentially with rank.
   At $x\ge0$, the negative order satisfies $\sqrt{q(x)}<\nu(x)\le C_*q(x)$.
   The first failing dimension $\kappa(x)\le\nu(x)+1$ has an explicit mixed-form lower horizon.
   The complete native rank-$N$ form has relative error $P_N/q$ with explicit quartic
   $P_N$, on $q\ge16(N+2)^2$; $q>2P_N$ leaves a strict half-Gaussian reserve.
   Every seam tail head is strict,
   with an explicit half-seam neighborhood and a separate strict distant ray.
   What are the sharp growth laws, and which native compensation pays the intervening
   compact-center integral as rank grows?

2. **Macroscopic overlap.** Can the actual completed Weil operator at a fixed nondegenerate ratio
   such as $3/2$ be compared to the cyclotomic Gram with cross-annulus and Schur costs paid?
   Can its certified prefix index ceiling be improved to positivity or an endpoint-sufficient
   upper index bound, along a profile-compatible exhaustive schedule?

3. **Census dispersion.** Can the actual bandwidth-$4/3$ coalescent surplus satisfy
   $(1/18+o(1))N$ in the receiver's windows, including model, cutoff, and collar errors?

4. **Euler deletion.** Which arithmetic relations control actual cumulative covariance and its
   infinite tail with subpower growth at the inner cutoff?

5. **Restricted completion.** Can the complete Suzuki rectangular Ward defect be bounded below on
   its natural domain? Can the actual CCM first-clock source have an eventual constant lower bound?

6. **Theta-clock history.** Can the source budget exclude every guarded zero? The guarded-zero set
   is unconditionally finite, so an eventual condition on that set is insufficient.

7. **Depth and index.** Can arithmetic readings give a sufficiently small Hecke-defect upper bound
   or an upper bound for the complete index? Height certificates detect index without bounding it.

8. **Strip precision.** Can actual normalized Chebyshev energy satisfy the $5/3+\varepsilon$ or
   $3/2+\varepsilon$ exponent bound? Can both detector Gram contributions enter the exact
   five-sixths feasible region?

9. **Transfer calculus.** Which concrete source maps preserve reserves, radicals, domains, and
   endpoint tolerances under simultaneous limits? The exact inverse-hyperbolic clock has an
   all-rank positive Gamma mixture while its physical pullback has finite failing rank.
   Its complete clocked cone has the exact boundary $(2q-3)^2\ge3$; all individual
   signed moments are nonnegative even outside that cone.
   The exact monic Hermite transform preserves relative complete-form bounds and pays
   the physical first-atom and infinite native errors by an explicit polynomial rank cost.
   Can Gaussian contraction estimates sharpen that cost to the quadratic degree scale?

These include RH-equivalent targets. Fixed-rank or fixed-parameter theorems contribute without
settling the full questions.

## Tools to develop

- Source residual estimates in the arithmetic Green norm; partial-conductor inverses and
  quantitative transfers from irregular arithmetic packets, retaining radicals and boundaries.
- Native successor estimates with rank-dependent reserves and controlled degeneracy.
- Completion theorems combining divergent signed channels on the correct domain.
- Arithmetic covariance estimates after accumulation, with exact tail control.
- Comparison inequalities tracking conductor, rank, aperture, profile, horizon, and cutoff together.
- Signed dispersion estimates for the actual centered census functional.
- Precision-preserving source bridges with all analytic inputs discharged.

## Traps

| Temptation | Mathematical obstruction |
|---|---|
| Spend the same reserve in several blocks | Combined Schur cost can exceed it |
| Ignore a comparison radical | A remainder can act on its null directions |
| Bound absolute successor rows uniformly | Actual fixed-overlap fibers grow logarithmically |
| Infer all-order positivity from finite theta sections | The complete signed hierarchy is RH-equivalent |
| Use a fixed fraction of each native-tail diagonal as reserve | The exact successor fraction tends to $N!/(s+\tfrac12+N)_N\le(2/3)^N$ |
| Keep only the first theta atom at all ranks | Every center has a negative signed moment; its least order escapes to infinity along the tail |
| Transport signed positivity through an invertible nonlinear clock | The exact Gaussian-clock first atom is positive at every rank while its physical pullback fails at a finite rank |
| Insert an arbitrary positive mixer | Faithful phase-natural mixing can be rigid or equivalent to the desired sign |
| Extend divergent positive masses to all sequences | No positive extension exists on that domain |
| Discard cross terms after coefficient estimates | Cumulative covariance measures unequal pairs |
| Replace actual prime evaluation by gauge variance | A prescribed gauge point need not satisfy an almost-everywhere budget |
| Use an eventual guarded-zero condition | The guarded-zero set is unconditionally finite |
| Exchange fixed and exhausting quantifiers | A growing schedule needs a joint horizon |
| Demand exact rigidity from a count theorem | Count permits the nontrivial class $\mathcal Q$ |

## Success and contribution criteria

A contribution proves an unconditional new source estimate, exact decomposition, sharp boundary,
classification, or transfer theorem. It specifies domain, normalization, radical, parameter range,
and arithmetic consequence. Source identifications and analytic inputs are discharged in Lean;
an unproved estimate cannot be hidden in a structure or imported hypothesis.

A comparison controls its complete remainder in the norm it uses. A limit retains relevant boundary
and cross terms. A negative result identifies its exact class and extracts a nontrivial positive
survivor. A source-independent lemma contributes when it supports a proved actual-source application.

Full success requires answers to the research questions and tools at their stated endpoint strengths.
A collection of criteria alone does not supply the missing inequalities.
