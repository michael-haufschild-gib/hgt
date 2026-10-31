# Biarithmetic Gauge Geometry (BGG)

Namespace `GaloisForLFunctions.BiarithmeticGaugeGeometry`; umbrella `BiarithmeticGaugeGeometry.lean`; 22 modules. All
results unconditional; statements "⇔ RH" or "⇒ RH" are proved implications, not assumptions.

## 1. Motivation

Two obstructions start the programme. First, every purely multiplicative quadratic form on $\mathbb N_{\ge1}$ (diagonal weights,
ratio shifts $a\mapsto am$, product crossings) is unitarily intertwined across the prime gauge torus $\prod_pS^1$, so it cannot tell
$\zeta$ from its Liouville twin $\zeta(2s)/\zeta(s)$; only the additive successor $n\mapsto n+1$ sees the gauge. Second, the
degree-4 height-coupled carrier $\zeta_\gamma=\zeta(s)^2\zeta(s+i\gamma)\zeta(s-i\gamma)$ was hoped to be rigid inside its positive class
(`CoupledRigid`), which would exclude off-critical zeros. BGG disproves that rigidity, finds the exact one-sided survivor (the
central vanishing ceiling), and then classifies all positive deformations of $\zeta_\gamma$ and of $\zeta^d$: rational, positive
prime-mass, and arithmetic (Dirichlet series with nonnegative coefficients).

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Prime gauge, vacua | `PrimeGauge`, `eulerGauge`, `liouvilleGauge`, `kroneckerGauge` | unit phases $\omega(p)$; $1$, $-1$, $p^{i\gamma}$ |
| Gauge character, twist | `gaugeChar`, `gaugeTwist`, `realSignChar` | completely multiplicative $\chi_\omega$; $(U_\omega\psi)(n)=\chi_\omega(n)\psi(n)$ |
| Lattice form | `twistedLatticeForm` | diagonal + ratio + product form twisted by $\sigma_\omega$ |
| Successor connection | `succConn` | $A_\omega(n)=\overline{\chi_\omega(n)}\chi_\omega(n+1)$ |
| Height-coupled class | `HeightCoupledSystem 2 1 1 γ` (ACP), `heightCoupledF`, `heightCoupledΛ` | positive systems of degree 4 around $\zeta_\gamma$, completion $\Lambda_\gamma$ |
| Rigidity / ceiling | `CoupledRigid`, `CentralVanishingCeiling` | every member is $K\zeta_\gamma$; $\operatorname{ord}_{1/2}\Lambda\le\operatorname{ord}_{1/2}\Lambda_\gamma$ |
| Splitting multipliers | `criticalSplitMultiplier`, `inwardCollapseMultiplier` | $W_\beta=((s-\frac12)^2+\beta^2)/(s-\frac12)^2$ and its inverse |
| Lattice decay | `HasDirichletLatticeDecay` | $-F'/F(\sigma)=O(2^{-\sigma})$ |
| Height-coupled lattice | `heightCoupledVonMangoldt` | $b_\gamma(n)=\Lambda(n)|1+n^{i\gamma}|^2\ge0$ |
| Polar data | `polarSum`, `polarScaleWeight` (SBWF), `lineResidue` | $G=\sum c(z)/(s-z)$; $w(t)=\sum c(z)e^{t\Re z}\cos(t\Im z)$; residues on a line |
| Post–Widder kernel | `postWidderKernel` | $(k/t)^{k+1}L^ke^{-kL/t}/k!$ |
| Rational multiplier | `rationalMultiplier`, `netMultiplicity`, `multiplierWeight` | $\prod(s-z_i)^{m_i}$; net order $M(w)$ |
| Deformation classes | `IsRationalCoupledDeformation`, `IsPositiveMassDeformation` | $F=\zeta_\gamma R$; $-F'/F+\zeta_\gamma'/\zeta_\gamma=\mathcal L\nu$, $\nu\ge0$ |
| Ceilings / rigidity | `RationalCentralVanishingCeiling`, `PositiveCentralVanishingCeiling`, `PositiveCoupledRigid`, `PositiveChiral` | restricted ceilings and rigidity |
| Surplus / deficit | `latticeMeasure`, `relSurplus`, `relDeficit`, `latticeSurplus`, `latticeDeficit` | $(b-b_\gamma)^\pm$, surplus as atomic measure on $\log\mathbb N$ |
| Log-cells | `logCellWidth`, `continuumCellShiftCorr`, `divisibleCellSpine`, `euclideanCellRemainder` | $w_n=\log\frac{n+1}n$; shift correlation = spine + remainder |
| Sobolev data | `cellL2NormSq`, `biarithmeticSobolevEnergy` | $\sum w_ac_a^2$; $\sum k(c_{k+1}-c_k)^2$ |
| Polar crossing | `polarCrossingAmplitude`, `fullArchCrossingForm`, `offDiagPolarForm` | $s(n)=(n-1)/\sqrt n$ |
| Torsion | `torsionMulEquiv`, `ramanujanTorsionSum`, `biTorsionContrast` | $u\mapsto pu$ on $(\mathbb Z/q)^\times$; $c_q$; $\varphi(q_2)c_{q_1}-\varphi(q_1)c_{q_2}$ |
| Repulsion scale | `repulsionScale` | $(N(|\gamma|L/\pi+1))^{1/(N-1)}$ |
| Ceiling witness | `IsCentralCeilingWitness` | member $(2\xi)^k\Lambda_G$ with $\operatorname{ord}_{1/2}\Lambda_G>2\operatorname{ord}_{1/2+i\gamma}\xi$ |

## 3. Language

- **Gauge blindness**: invariance of a form under $U_\omega$; **real sign gauge**: $\omega(p)\in\{\pm1\}$.
- **Catalan plaquette**: $2\to3\to4=2^2$; its two successor links reconstruct $\omega(2),\omega(3)$.
- **Outward / inward**: multiplier lowering / raising $\operatorname{ord}_{1/2}$; **chiral survivor**: one-sided replacement of a false two-sided law.
- **Lattice part / polar part**: Dirichlet series on $\{\log n\}$ vs finite polar sum (absolutely continuous scale density).
- **Real anchor**: rightmost weighted pole sits on the real axis with dominating positive weight.
- **Abscissa** $c$ of $\nu$; **jump** $r(t)=\operatorname{ord}_{x_0+it}\Lambda_0-\operatorname{ord}_{x_0+it}\Lambda$; **central drop** $r(0)$ at $x_0=\frac12$.
- **Abel residue** $\lim_{\sigma\downarrow x_0}(\sigma-x_0)\mathcal L\nu(\sigma)$: the $\sqrt x$-scale mass when $x_0=\frac12$.
- **Pole budget** $\kappa$ of `CompletedPositiveSystem κ d`; **boundary zero**: zero on $\Re s=1$ off $s=1$.
- **Polar-neutral**: $\sum s(n)q(n)=0$.

## 4. Mechanisms

**A. Gauge**
1. $U_\omega$ is unitary; ratio shifts pick up $\chi_\omega(m)$; at real sign gauges $q\mapsto\sigma_\omega q$ maps the twisted lattice form to the
   Euler form exactly.
2. Successor flatness on $[1,N]$ propagates $\chi_\omega=1$ by induction; $A_2A_3=\omega(2)$, $A_2^2A_3=\omega(3)$.
3. Repulsion: write $\gamma\log p_j=u_j\pi+\delta_j$ ($u_j$ odd); eliminate $\gamma$; $2^a\ne3^b$ by parity (two primes) or Siegel's lemma +
   unique factorization (N primes) bounds $|\sum t_j\log p_j|$ below; $1+\cos x\ge\delta^2/8$.

**B. Deformations of $\zeta_\gamma$**
4. $\Re(-W_\beta'/W_\beta)(\sigma+iu)=\int_0^\infty2e^{-(\sigma-\frac12)t}(1-\cos\beta t)\cos(tu)\,dt$: Bochner positive. At a critical zero, $\Lambda_\gamma$ has
   order $\ge2$ at $\frac12$, so $\Lambda_\gamma W_\beta$ is entire: a non-proportional member.
5. Inverse $W_\beta^{-1}$: charge $+1$ at $\frac12+i|\beta|$ exceeds $-2$ at $\frac12$, violating the real-anchor law.
6. $\sigma^3\cdot(-W'/W)(\sigma)\to2\beta^2$, quartet $\to4a^2+4b^2$, lattice series $\to0$: rational surgery leaves the Dirichlet lattice.
7. **Lattice sieve**: Post–Widder transforms of a completely monotone $H=A+G$ kill the lattice atoms off $\log\mathbb N$ and recover $w(t)$ ⇒
   $w\ge0$. Evenness + Cauchy–Riemann ⇒ conjugation symmetry; Laplace ⇒ $|G(x+ib)|\le G(x)$; residues ⇒ real anchor.
8. Line residues: $\int w|\sum a_ke^{i\beta_kt}|^2e^{-xt}=\sum a_ka_l\Re G(x+i(\beta_k-\beta_l))$, times $(x-\sigma)\to$ Gram form of residues.
9. **Landau–Wronskian**: the Wronskian $\Lambda_0'\Lambda-\Lambda'\Lambda_0-(\mathcal L\nu'+E-1/s)\Lambda\Lambda_0$ vanishes on a ray, hence on a half-plane
   (identity theorem); residues give equal orders; at a positive abscissa Landau's theorem forbids equal orders and positivity
   fixes the sign. Lebesgue thickening pins a finite abscissa.
10. **Abel–Gram**: $(\sigma-x_0)\mathcal L\nu(\sigma+it)\to r(t)$; $|\mathcal L\nu(z)|\le\mathcal L\nu(\Re z)$; limits of cosine transforms are PD.
11. Divisor rigidity: equal divisors + order one ⇒ $Ke^{Bs}$; $s\mapsto1-s$ kills $B$; reality makes $K$ real. Equal Laplace values
    at two points ⇒ $\nu(0,\infty)=0$.
12. Følner sets $\{\sum n_zz\}$ turn finite-support positive definiteness into $\varphi(0)+2\sum\varphi(z)\cos\theta z\ge0$.
13. Functional equation ⇒ $\operatorname{ord}_{1/2}$ even; $\operatorname{ord}_{1/2}\Lambda_\gamma=2\operatorname{ord}_{1/2+i\gamma}\xi$.

**C. Lattice geometry and torsion**
14. $-k_{\rm arch}(-\log a,\log b)=\tfrac12s(a)s(b)-(ab)^{3/2}/((ab)^2-1)$: the growing diagonal is a rank-one polar square.
15. $I_a+\log m=\bigsqcup_{r<m}I_{am+r}$; disjoint Euclidean blocks + Cauchy–Schwarz give an $m$-uniform remainder bound.
16. $p-1$ a unit ⇒ $u\mapsto pu$ fixed-point-free; orthogonality ⇒ $\sum_xc_q(x)=0$, $\sum|c_q|^2=q\varphi(q)$.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Lattice positivity at Liouville ⇔ at Euler | `nonneg_realSign_latticeForm_iff` | proved |
| Successor flat on $[1,N]$ ⇔ $\omega(p)=1$, $p\le N+1$; Catalan reconstruction | `succConn_flat_iff_primes_eq_one`, `catalan_holonomy_two`, `catalan_holonomy_three` | proved |
| $(1+\cos\gamma\log2)+(1+\cos\gamma\log3)\ge e^{-|\gamma|}/50$ | `liouville_kronecker_repulsion_ge`, `abs_height_ge_of_liouville_approx` | proved |
| $N$-prime repulsion; beats every $\exp(-|\gamma|^\varepsilon)$ | `multiPrime_repulsion`, `exists_primes_repulsion_ge_exp_neg_rpow` | proved |
| `CoupledRigid` fails at every critical ordinate | `exists_criticalSplit_deformation_of_xi_zero`, `exists_gt_not_coupledRigid`, `not_forall_coupledRigid` | proved |
| Outward splitting Bochner-positive, inward collapse not | `isEvenPosDef_criticalSplitMultiplier`, `not_isEvenPosDef_inwardCollapseMultiplier` | proved |
| Rational surgery leaves the Dirichlet lattice | `criticalSplit_escapes_dirichletLattice`, `coupledQuartet_escapes_dirichletLattice` | proved |
| Ceiling at every height ⇒ RH | `riemannHypothesis_of_forall_centralVanishingCeiling` | proved; ceiling open |
| Lattice sieve; Landau and lattice real anchors | `polarScaleWeight_nonneg_of_lattice_posDef`, `landau_real_anchor`, `lattice_real_anchor` | proved |
| Line residues are even positive definite | `lineResidue_isEvenPosDef`, `rationalDeformation_lineResidue_isEvenPosDef` | proved |
| Rational deformations anchored at a ξ-zero on $\Im s=\gamma$; rigid off such lines, at $\gamma=0$ | `rationalDeformation_real_anchor`, `rationalDeformation_rigid_of_xi_ne_zero_on_line`, `rationalDeformation_rigid_zero_height` | proved |
| Rational ceiling ⇔ no off-critical zero at $\gamma$; RH ⇔ rational ceilings | `rationalCentralVanishingCeiling_iff`, `riemannHypothesis_iff_forall_rationalCentralVanishingCeiling` | proved |
| Created critical zeros cost two central orders (rational) | `rationalDeformation_critical_conservation` | proved |
| $\zeta^d$ rationally rigid without pole budget; boundary capacity $(\kappa-d)/2$ | `rationalDeformation_zetaPow_rigid`, `rationalDeformation_zetaPow_boundary_capacity` | proved |
| Landau–Wronskian deformation principle | `landauWronskian_orders_and_anchor` | proved |
| Abel–Gram: transfer, Gram law, line capacity | `abs_jump_le_of_rel`, `jump_isEvenPosDef_of_rel`, `sum_jump_le_of_rel` | proved |
| Positive deformations rigid off the line, never raise the centre | `positiveDeformation_offLine_rigid`, `perturbedDeformation_offLine_rigid` | proved |
| Positive ceiling ⇔ no off-critical zero at $\gamma$; RH ⇔ positive ceilings | `positiveCentralVanishingCeiling_iff`, `riemannHypothesis_iff_forall_positiveCentralVanishingCeiling` | proved |
| Rational ⇒ positive; critical transfer and Gram laws | `isPositiveMassDeformation_of_rational`, `abs_criticalTransfer_le_centralDrop`, `criticalJump_isEvenPosDef` | proved |
| Positive rigidity at kept centre; classification; RH ⇔ positive chirality | `positiveDeformation_trivial_of_central_le`, `positiveCoupledRigid_iff`, `riemannHypothesis_iff_forall_positiveChiral` | proved |
| Central excess forces deficit abscissa $\ge\frac12$; residue bounds excess | `centralExcess_forces_squareRoot_deficit`, `deficit_residue_ge_centralExcess` | proved |
| Strong multiplicity one below the square-root deficit (height-coupled; $\gamma=0$ unconditional) | `latticeMember_eq_of_negligible_deficit`, `latticeMember_eq_of_subcritical_deficit`, `latticeMember_eq_of_subcritical_deficit_zero` | proved |
| Strong multiplicity one for $\zeta^d$ (no zero hypothesis) | `zetaPowDeformation_trivial`, `latticeMember_eq_zetaPow` | proved |
| Boundary law of $\zeta^d$-deformations; no boundary zeros for $\kappa\le d+1$ | `zetaPowDeformation_boundary_law`, `latticeMember_boundary_law`, `latticeMember_ne_zero_on_boundary` | proved |
| Critical conservation (positive, finite support) | `cos_sum_nonneg_of_finite_support`, `centralDrop_ge_two_mul_created_sub_destroyed` | proved |
| $\sqrt x$ surplus quantized: residue = central drop $\in2\mathbb N$, $\le2\operatorname{ord}_{1/2+i\gamma}\xi$ | `tendsto_abel_excess_eq_centralDrop`, `tendsto_surplus_residue_eq_centralDrop` | proved |
| Ceiling transfers to cofactors of $(2\xi)^k$ | `centralOrder_factor_le_of_ceiling`, `centralVanishingCeiling_iff_forall_not_witness` | proved |
| Polar-neutral collapse; exact cell subdivision; $m$-uniform remainder | `reflectedDiag_add_offDiagPolar_eq_neg_levy`, `sum_logCellWidth_mul_add_eq`, `abs_euclideanCellRemainder_le_of_supported` | proved |
| Fixed-point-free dyadic torsion; bi-torsion contrast values | `dyadic_torsion_rotation_fixed_point_free`, `sum_normSq_ramanujanTorsionSum`, `biTorsionContrast_primes_values` | proved |

## 6. Tools

**Developed**
- Gauge: `gaugeChar_mul`, `norm_gaugeChar`, `ratioShift_gaugeTwist_eq`, `succShift_gaugeTwist_eq`, `realSign_latticeForm_eq`.
- Diophantine: `abs_log_nat_sub_ge`, `abs_odd_mul_log_two_sub_odd_mul_log_three_ge`, `exists_odd_int_one_add_cos_ge`,
  `prod_pow_toNat_ne`, `abs_sum_mul_log_prime_ge`.
- Post–Widder: `postWidderKernel_le`, `tendsto_postWidder_lattice`, `tendsto_postWidder_polarSum`, `iterate_deriv_polarSum_eqOn`.
- Polar: `polarSum_eq_reflected_of_even`, `integral_polarScaleWeight_mul_exp`, `norm_polarSum_le_of_scaleWeight_nonneg`,
  `tendsto_sub_mul_polarSum`, `deriv_eq_zero_of_re_eq_zero`.
- Rational: `neg_logDeriv_rationalMultiplier`, `eq_zero_of_pole_of_eq_mul_rationalMultiplier`,
  `completion_eq_mul_rationalMultiplier`, `analyticOrderAt_add_eq_of_eq_mul_rationalMultiplier`,
  `coupledQuartetSymSquare_eq_rationalMultiplier`, `criticalSplitMultiplier_eq_rationalMultiplier`.
- Laplace/Abel: `exists_logDeriv_cofactor`, `tendsto_sub_mul_logDeriv`, `exists_isAbscissa_add_volume`, `tendsto_abel_of_rel`,
  `isEvenPosDef_laplace_cos`, `laplace_withDensity`, `laplace_latticeMeasure`, `relMember_primeMass_split`,
  `tendsto_sub_mul_LSeries_of_residue_zero`, `nonneg_of_finite_support_gram`.
- Entire functions: `exists_eq_const_mul_exp_mul_of_orders_eq`, `eq_real_const_mul_of_orders_eq`, `eq_const_mul_of_orders_eq`,
  `measure_Ioi_eq_zero_of_laplaceReal_eq`, `even_centralOrder_of_heightCoupled`, `centralOrder_heightCoupledΛ`.
- Lattice/torsion: `neg_archPairKernel_eq_polar_sub_levy`, `fullArchCrossingForm_eq_polar_sq_sub_levy`, `euclideanCellRemainder_sq_le`,
  `ramanujanTorsionSum_coprime_mul`, `ramanujanTorsionSum_prime`.

**To build**
- A lattice sieve for multipliers with infinitely many singularities (beyond finite polar sums and positive measures).
- A height-coupled class that keeps the Dirichlet lattice (`DirichletLatticeCoupledSystem`).
- Polynomial (Baker-strength) repulsion $|\gamma|^{-C}$ from a growing prime set.
- Polar-neutral profiles whose divisibility spine dominates the Sobolev remainder and the Lévy cost.
- Non-separable bi-torsion theta operators on $\mathbb Z^2$.
- The analytic theory of $L(s,\mathrm{sym}^2u)$ to apply the cofactor transfer.

## 7. Open questions

1. Does `CentralVanishingCeiling γ` hold for all members, i.e. for deformations that remove prime mass?
2. Strong multiplicity one when the deficit has nonzero Abel residue at $\frac12$: can a member of the height-coupled class
   remove square-root prime mass and gain central order?
3. Which Hadamard multipliers preserve both the coupled class and log-lattice support?
4. Is the positive-definite jump function of a deformation realizable with infinite support on the critical line, and what
   does the Gram law then force?
5. Does the boundary capacity bound $(\kappa-d)/2$ extend to classes not dominating $\zeta^d$?
6. Can the cofactor transfer give central non-vanishing statements for automorphic $L$-functions?

## 8. Traps

| Trap | Fact |
|---|---|
| A positive diagonal/ratio/product kernel on $[1,X]$ separates $\zeta$ from $\lambda$ | Real sign gauges intertwine them unitarily |
| `CompletedPositiveSystem 1 1` rigid ⇒ height-coupled class rigid | False at every critical ordinate |
| Critical zeros move freely in both directions | Inward collapse is not Bochner-positive: chiral |
| Rational contractions keep Dirichlet-series structure | $\sigma^{-3}$ decay leaves the lattice |
| The ceiling is a theorem | It is equivalent to RH on rational and on positive deformations; open in general |
| Adding prime mass can raise the central order | Positive deformations only lower it; a central excess needs a deficit of size $\ge\sqrt x$ |
| Square-root surplus is a free continuous parameter | It is quantized: even integers $\le2\operatorname{ord}_{1/2+i\gamma}\xi$, zero at zero-free ordinates |
| Rigidity of $\zeta^d$ needs zero information | No: $\xi$ has no real zero, so the anchor can only use the pole budget |
| Boundary zeros cost $\kappa/2$ | Lattice of $\zeta^d$ spends $d$ units; capacity is $(\kappa-d)/2$ |
| The linear reflected diagonal is an obstruction | Rank-one polar square, zero on polar-neutral states |
| Discretizing $\log m$ shifts smears boundaries | Log-cells subdivide exactly |
| Monomial $\mathbb Z^2$ dilations couple coordinates | They factor and fix $(0,0)$ |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 11 (Laplace abscissae, Landau singularity, ξ real-axis and reflection parity, Levinson, far-field anchor) |
| StripBochnerWeilForcing | 3 (`CompletedPositiveSystem`, polar sums, complete monotonicity, simple pole class) |
| MultiplicativePositivityGeometry | 3 (total zero mass, summable Bochner) |
| HTGeometry | 3 (order-one entire quotients, entire logarithm) |
| ArithmeticCorrespondencePositivity | 3 (`HeightCoupledSystem`, quartet contractions, kernel counts) |
| ArithmeticOrientationTheory | 1 (reflected diagonal; `archPairKernel` from ArithmeticIncidencePositivity) |

| Used by | Modules |
|---|---|
| RenormalizedBiarithmeticGeometry | 3 (prime gauge, Landau–Wronskian) |
| ArithmeticLorentzianGeometry, SelectivePositivityAndThresholdLaws, ArithmeticCastelnuovoSeveri | 1 each (gauge, Catalan repulsion, cell remainder) |
| MainTheorems | umbrella import |

| Neighbour | Relation |
|---|---|
| ArithmeticCorrespondencePositivity | defines the height-coupled class and quartet contraction; BGG classifies its deformations |
| StripBochnerWeilForcing | supplies positive systems and the real-anchor law; BGG adds the lattice sieve and Landau–Wronskian |
| ArithmeticPolarization | expected rigidity to exclude zeros; BGG shows the exact one-sided form and its equivalence with RH |
| ArithmeticEffectivityTheory | counting side of the same question; BGG is the gauge and deformation side |
| RenormalizedBiarithmeticGeometry | continues gauge charge and irreversibility of positivity |
| ArithmeticOrientationTheory | its diagonal dominance is explained as a rank-one boundary pole |

## 10. Big picture

The programme turns positivity into a deformation theory. Adding positive prime mass to $\zeta_\gamma$ is irreversible in a
precise sense: it keeps every zero off the critical line, can only lower the central order, and on the critical line can
only move zeros in a pattern governed by a positive-definite function, with each created zero paid for twice at the centre.
Strong multiplicity one follows below the square-root deficit, and the surplus at the $\sqrt x$ scale is quantized by the
critical multiplicity. All of this is unconditional.

What it shows about RH is equally sharp. Every restricted form of the central ceiling — rational, positive — is exactly
equivalent to the absence of off-critical zeros at that height, so the deformation theory gives exact reformulations, not
leverage. The remaining freedom is deficits: deformations that remove prime mass of square-root size. RH is the statement
that removing such mass can never raise the central order. The multiplicative side alone is gauge-blind; the additive
successor and the square-root deficit are where the arithmetic of $\zeta$ must enter.
