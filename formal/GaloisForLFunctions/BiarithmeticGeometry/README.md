# Biarithmetic Geometry (BG)

Namespace `GaloisForLFunctions.BiarithmeticGeometry`; umbrella `BiarithmeticGeometry.lean`.

**Question.** Does the joint additive and multiplicative action of the integers at finite horizon supply
signed arithmetic estimates that disappear when one keeps only multiplicative identities, complete-period
quadratic data, or a limiting energy?

Target: the critical arithmetic form shared by the corpus's RH approaches. An exact finite identity is a
foundation; an independent estimate uniform in the horizon is still required. BG keeps four things together
— the **horizon**, **signed linear data**, **both ring operations**, **integer invariants** — and seeks a
source-derived relation between them and the analytic norm, or an exact classification of why a proposed
relation fails.

---

## 1. Place in the research

Over $\mathbb F_q$, Frobenius is a ring map and point counts come from a complete finite object. Over $\mathbb Z$,
divisor incidence on $\{1..N\}$ has period $L_N=\operatorname{lcm}(1..N)$; completing it changes the observation scale.
Complete-period quadratic data lose signs (BVI); normalized escape limits keep dilation but lose fixed
successors (ADR); local prime-power payments need not share resources (AIP). BG studies the ring action at
the horizon itself, and builds the payment/escape algebra of explicit calibration sources (prime-five towers,
the golden datum).

| Programme | Interface |
|---|---|
| BezoutValuationIncidence | Divisor rows, Selberg coordinates, complete-period blindness |
| TransHorizonIncidenceMechanics | Centred prefixes, critical Wiener convolution, additive selectivity |
| ArithmeticDefectRigidity | Escaping energies, common cofactor Gram limits, Wiener modules |
| ArithmeticOrientationTheory | $\mathcal W_{1/2}$, paid ideals, Bohr hulls, box invariant $E(s)$ |
| ArithmeticCastelnuovoSeveri | Golden datum, effectivity, $\mathbb F_q$ calibration |
| ArithmeticIncidencePositivity | Local prime-power payments, shared surplus, two-pole Chebyshev defect |
| RenormalizedBiarithmeticGeometry | Renormalized Hecke defects, Ramanujan germs (continuation of BG) |

---

## 2. Objects and language

- **Horizon space** `HorizonSpace N`: cells $\{0..N\}$, $e_j=0$ for $j>N$ (absorption); no quotient mod $N$.
- **Affine pushforward** $T_{(a,b)}e_j=e_{aj+b}$; successor $U=T_{(1,1)}$, dilation $D_a=T_{(a,0)}$.
- **Box invariant** $E(s)=e^s+s-1-\psi(e^s)$ (real-valued); horizon torsion $Q_N=L_N/N$.
- **Prime-five calibration**: weighted digit rows $D_a(n)$ (base-5 digits at $a$); tower source $I_a(5^r)=a^r$;
  kernel lifts $k(5^r)=f_r$; critical lift $k_g(5^r)=\sqrt5^rg_r$.
- **Golden source** at $t$: $a=\alpha t$, $b=\beta t$, `goldenArithmeticSource` $=\delta_1-I_a/\sqrt5+I_b/\sqrt5$.
- **Cofactor action** $P_k(n)=\sum_{j\le n}k(j)A(\lfloor n/j\rfloor)$; **paid ideal**; **cofactor graph domain** in $\mathcal W_{1/2}\times\ell^2$.
- **Escape modules**: completions of finite cofactor packets in their limiting Gram norm with $\mathcal W_{1/2}$ acting by
  dilation (ADR). Arbitrary positive kernels with dilation bounds are calibration models, not escape states.
- **Logarithmic chirps**: phases $n\mapsto e^{i\beta(\log n)^2}$-type orbits; chirp Cauchy kernels.
- Payment obstructions: ambient $H^1$, adverse index, capacity deficit and real weighted Euler invariant are
  four different objects.

---

## 3. Mechanisms

### Affine geometry of the horizon
1. **Exact composition** $T_{(a,b)}T_{(c,d)}=T_{(ac,ad+b)}$, $D_aU=U^aD_a$; exactly $1+(N+1)(N+2)/2$ operators (no period).
2. **Joint rigidity**: common commutant of $U,D_2$ is scalar; invariant subspaces are the $N+2$ tails —
   indecomposable, not irreducible.
3. **Exact boundary loss** of the pairing under affine maps; successor-invariant observables are constant.
4. **Normalization freedom**: every multiplicative character twist preserves the action — covariance cannot select
   the analytic normalization.
5. **Unitary rigidity**: nontrivial translation limits need infinite rank.

### Arithmetic Euler characteristic
6. **Not an ordinary index**: $E(\log3/2)\in(0,1)$, so no $\mathbb N$-valued $h^0-h^1=E$.
7. **Degree minus log torsion**: $E(\log N)=(N-1)-\log\#(\mathbb Z/Q_N)$; period reductions have cyclic kernels of
   log-order $\Lambda(N+1)$.
8. **Shared-budget descent**: singleton-admissible allocations glue iff $k\le1$ or $B=0$; sharp excess $kB$.

### Visibility and domains
9. **Exact prefix visibility**: rows with equal complete-period covariance have centred prefixes within
   $V_N=\sum_q|R_q(M)Y_q|$, diameter exactly $2V_N$.
10. **Diagonal scaling does not determine the metric** (non-homogeneous cyclic dilation model; stationary averaging
    restores homogeneity).
11. **Prime-log jump domain**: $\sum_pw_p\|f-\tau_{\log p}f\|^2<\infty$ iff weights summable or $f=0$.
12. **Pronic energy domain**: admission = summable cell energies; the cofactor graph is closed, its input image is the
    paid ideal, Wiener-closed iff a uniform output bound holds; payment ⇔ bounded full cofactor action.
13. **Pronic dilation representation**: $\|D_jf\|=\|f\|/\sqrt j$, $D_jD_k=D_{jk}$, integrating to a unital $\mathcal W_{1/2}$
    representation; paid perturbations leave the repairing ideal unchanged.

### Escape-module bridge
14. $P_k=A_{k\star c_\varepsilon}-m_\varepsilon A_k$; on escape every repairing kernel's action vanishes after normalization, so actual
    common-limit annihilators contain the paid ideal and hulls lie in the obstruction hull.

### Prime-five / golden laboratory
15. **Digits.** $D_a(5n+r)=r+aD_a(n)$; self-similar limit profiles; tower prefix $=-a/(5-a)\cdot D_a(n)$; leading digit
    variance cannot be cancelled.
16. **Admission threshold**: tower paid ⇔ $|a|<\sqrt5$; golden source paid ⇔ $\alpha t<\sqrt5$.
17. **Payment criterion**: $k(5^r)=f_r$ repairs $I_a$ ⇔ $\sum(a^2/5)^l(\sum_{r\le l}f_r/a^r)^2<\infty$; at criticality ⇔ partial
    sums square-summable.
18. **The critical paid ideal is not closed.** Zero-sum repairs converge to an unpaid kernel; closure = kernel of total
    evaluation; the continuous dual of the unreduced quotient is one-dimensional, but the payment quotient and
    closure defect both have Hamel dimension continuum (power tails with exponents in $(0,\tfrac12)$).
19. **Golden source algebra.** Exact inverse coefficients; golden paid ideal = primary tower's; calibration depends on
    the counting kernel (intrinsic vs ordinary floor); normalized cube $z\mapsto z^3/5$ gives negative point counts.
20. **Shells and causal division.** Five-shell rows have finite energy iff every ordinary pronic norm is bounded;
    complex shell shifts are isometric with additive indices; expanding causal responses have finite energy exactly
    on the reciprocal evaluation kernel.
21. **Chirps.** Three-rotation rigidity of complex amplitudes; the logarithmic chirp orbit closure is a compact group
    of completely multiplicative phases; finite chirp Cauchy matrices at distinct cofactors are positive definite.

---

## 4. Pillar theorems

1. **Affine horizon geometry** (`horizonAffine_comp`, `card_horizonAffine_image`, `horizon_joint_commutant`).
2. **Arithmetic Euler formula** (`no_dimension_model_for_boxDefect`, `boxDefect_eq_degree_sub_log_torsion`).
3. **Exact visibility** (`prefix_visibility_diameter`).
4. **Payment = graph domain** (`paidIdeal_iff_existsUnique_cofactorGraph`, `isClosed_range_cofactorGraphInput_iff`).
5. **Module–ideal bridge** (`admits_or_all_actual_moduleHulls`).
6. **Prime-five / golden payment classification** (`receiverBounded_fiveTower_abs_iff`,
   `receiverBounded_fiveTowerKernelLift_iff`, `not_isClosed_golden_critical_paidIdeal`,
   `rank_criticalGoldenPaymentQuotient_eq_continuum`).
7. **Chirp positivity** (`chirpCauchyKernel_posDef`).

---

## 5. Traps

1. Affine identities need a normalization: character twists preserve them.
2. $E$ is degree minus log torsion, not a dimension.
3. Local existence is not a sheaf axiom; restrictions and gluing must be proved.
4. Curve $H^1$ has dimension $2g$ under RH; a purity obstruction must be a different group or adverse part.
5. Truncations of a repairing kernel need not repair; use the full-action norm bound.
6. A finite Gram limit does not control moving tails; white noise has a unique antipodal extension.
7. Structural (Class III) selectivity is not source selectivity.
8. Paid ideals need not be closed; zero evaluation is weaker than critical payment.
9. Golden calibration depends on the counting kernel.
10. Square-root energy scale for moving successors is excluded (ADR).

---

## 6. Open problems

- **Horizon-complete observation**: sign visibility between prefix and full period at polynomial horizon.
- **Escape classification**: classify actual common-limit Wiener modules; compare annihilators with paid ideals.
- **Critical translations**: a scale beyond $k^{1-\varepsilon}$ at which moving successors keep source information.
- **Arithmetic payment theory**: an allocation complex keeping shared capacity, with integer obstruction related to
  degree/torsion; exact sequences, duality.
- **Quantitative Class III**: bound signed off-diagonal Vaughan entries using joint $+/\times$ structure.
- **Stepanov at integer horizon**: a simultaneous prime-power vanishing mechanism failing for parity twins.
- **Infinite-rank coercivity**: transfer prime-coordinate bounds to the dense logarithmic (chirp) orbit.
- **Orientation**: an independently positive polarization compatible with ring action and normalization.

## 7. Tools to build

An allocation complex with an integer obstruction; a Class III off-diagonal estimate; a coercivity transfer from
prime coordinates to the chirp orbit.

## 8. Selectivity and success criteria

Battery: genuine curves, golden datum, Beurling systems with off-line zeros, shifted pairs, single-prime Euler
deformations, parity twins, node deletions $\log4$, $\log6$. Affine theorems are structural (Class III); the Euler
formula uses actual weights; neither is an orientation theorem. Full success: recover curve $H^1$ and duality with
the right obstruction; pass the battery; recover PNT, VK and Guth–Maynard density in source coordinates; produce new
unconditional analytic output or an actual escape-family classification. Name source object and horizon, keep
signs, state the selectivity class, separate structural classification from analytic estimate.
