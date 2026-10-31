# Arithmetic Polarization (APol)

Namespace `GaloisForLFunctions.ArithmeticPolarization`; umbrella `ArithmeticPolarization.lean`; 29 modules. All results
unconditional; statements "⇔ RH" are proved equivalences.

## 1. Motivation

Over $\mathbb F_q$ the sign of the explicit formula comes from a polarization: the Rosati trace form is at once positive
and Frobenius-equivariant, and the polarization law turns this into purity. Over $\mathbb Z$ every other Weil layer
exists (ACP) and every positivity built from invariance is isotropic at off-line pairs. APol asks what could play the
polarization over $\mathbb Z$: which symmetries localize at an off-line pair without being hyperbolic, what positive
forms the test space of $\zeta$ actually carries, and what positive completions of charged weights can and cannot do.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Polarization | `IsPolarization` | $\tau(v'v)$ real, $\ge0$, zero only at $0$ |
| Reflection-closed spectrum | `ReflSpectrum`, `refl`, `rosatiForm` | finite $S\subset\mathbb C^\times$ closed under $\beta\mapsto1/\bar\beta$; $\sum m\,\overline{x(1/\bar\beta)}x(\beta)$ |
| Spectral collided form / defect | `ReflSpectrum.collided`, `ReflSpectrum.defect` | $\sum m|x(\beta)|^2$; $\sum\frac m2|x(\beta)-x(1/\bar\beta)|^2$ |
| Rosati reflection | `rosatiRefl` | $s\mapsto1-\bar s$ |
| Point reflection, flow | `sigma`, `tau` | $\sigma_\gamma(s)=1+2i\gamma-s$; $\tau_\kappa(s)=s+i\kappa$ |
| Twisted symmetric symbol | `twistedSymSymbol` | $p^{s-1/2}+p^{2i\gamma}p^{1/2-s}$, scalar on pairs of ordinate $\gamma$ |
| Transform, twist, localizer | `tr`, `twist`, `fe`, `sigmaTest` | $\int f e^{(s-1/2)u}$; $e^{-i\gamma u}f$; $f(-u)$; $e^{-2i\gamma u}f(-u)$ |
| Shifted configuration | `shiftConfig` | $Z-i\gamma$ as a `Zeta23.ZeroConfig` |
| Collided form, off-line defect | `collidedForm`, `offLineDefect` | $D(f)=\sum m_\rho|\hat f(\rho)|^2$; $\Delta(f)=\sum\frac{m_\rho}2|\hat f(\rho)-\hat f(1-\bar\rho)|^2$ |
| Exterior point | `extPoint` | $\rho+\rho'-\tfrac12$; collided point $2\Re\rho-\tfrac12$ |
| Coupled datum | `coupleDatum` | $D\otimes(e^{i\theta}\oplus e^{-i\theta})$ |
| Leading line | `leadingSum`, `offLeadingSum`, `leadingPoly`, `cosPoly` | $T_\sigma(t)=\sum_{\Re z=\sigma}c(z)\cos(\Im z\,t)$ |
| Coupled rigidity | `CoupledRigid` | every member of `HeightCoupledSystem 2 1 1 γ` is $K\zeta_\gamma$ |
| Depth profile | `depthProfile`, `depthWeight`, `depth`, `seenDepth` | $L\mapsto D(T_Lf)$, Laplace transform of the depth measure |
| Low-frequency mass | `lowMass` | $\int_{-T}^T|\hat f|^2$ |
| Fake spectra | `goldenSpectrum`, `complexFakeSpectrum` | $\{\varphi,\varphi^{-1}\}$; $\{\pm2i,\pm i/2\}$ |
| First-twin ordinate | `γ₂`, `poleTerms`, `archTerm` | $\pi/\log2$ |

## 3. Language

- **Equivariant form**: Weil's form $W$; Hecke translations are its isometries. **Positive form**: the collided form $D$.
- **Local type at an off-line pair**: hyperbolic (boost, isotropic), elliptic (swap $\sigma_\gamma$, definite), collided
  (determinant, positive and sign-blind).
- **Even / odd sector** of $\sigma_\gamma$: twists of even / odd tests; even = blind half, odd = forcing half.
- **Conductor**: shift of the digamma density under a twist ($\asymp\log\gamma$). **Conductor horizon**: aperture
  $a$ with $(4+\varepsilon)e^a\approx\log\gamma$.
- **Gauge charge**: phased prime weights $\Lambda(n)\cos(\gamma\log n)$ with negative values.
- **Positive completion**: polar configuration with PD vertical sections; **harmonic lift**
  $\prod_kF(s\pm ik\gamma)^{b_k}$; **coupling**: completion whose kernel counts are modulus squares.
- **Collision parity**: even (couplings, height coupling) vs odd (exterior square).
- **Diagonal collapse**: two-variable lattice counts see only $s_1+s_2$ or factor.

## 4. Mechanisms

**A. Polarization algebra**
1. Polarization law: $\xi'\xi=c$, $\xi v=\mu v$, $\tau(v'v)\ne0$ ⇒ $|\mu|^2=c$; only anisotropy is used.
2. Polarization identity $2\Re(u\bar v)=|u|^2+|v|^2-|u-v|^2$ summed over zeros: $\Re W=D-\Delta$.
3. Translation $T_L$ multiplies $\hat f(\rho)$ by $e^{(\rho-1/2)L}$; the product with the reflected conjugate is $1$
   ($W$ invariant), while $D$ picks up $e^{2(\Re\rho-1/2)L}$.

**B. Elliptic localization**
4. Affine classification: maps commuting with $s\mapsto1-\bar s$ that send an off-line point into its pair are the
   identity and $\sigma_\gamma=\tau_\gamma\circ(1-\cdot)\circ\tau_{-\gamma}$.
5. Definite sectors: $G\circ\sigma_\gamma=\pm G$ ⇒ local form $\pm2|G(\rho)|^2$.
6. Dihedral dilemma: boost lemma applied to $(x,y)$, $(x+y,\cdot)$, $(x+iy,\cdot)$ ⇒ boost + swap blind the pair.
7. Twist identity: $Z.W(e^{-i\gamma u}f)=(Z-i\gamma).W(f)$; twisted explicit formula has shifted poles, phased primes,
   shifted digamma.
8. Charge: for $\gamma\ne0$ some $2^k$ or $3^k$ has $\cos(\gamma\log n)<0$ ($2^b\ne3^a$).

**C. Collision**
9. $\rho+\bar\rho-\tfrac12=2\Re\rho-\tfrac12$: depth doubled, ordinate forgotten; points accumulate in $[-\tfrac12,\tfrac32]$
   or pile up ⇒ identity theorem kills any analytic carrier.
10. Coupling kernel counts pair $\beta e^{i\theta}$ with $\bar\beta e^{-i\theta}$ ⇒ modulus squares; height coupling has orders
    $2\operatorname{ord}_x+2\operatorname{ord}_{x+i\gamma}$ at real $x$.
11. Cauchy denominators $2x+i(y_k-y_l)=\operatorname{ext}(z_k,\bar z_l)-\tfrac12$: escape forms are Pick forms.

**D. Positive cone of polar configurations**
12. Laplace identity: PD sum $=\int_0^\infty e^{-\sigma t}|\sum w_ie^{-ix_it}|^2w(t)dt$; Bochner uniqueness ⇒ one section
    decides.
13. Post–Widder + Bohr large returns ⇒ leading line $T_{\sigma_{\max}}\ge0$; periodicity on lattice ordinates ⇒ line
    hierarchy.
14. Fejér–Riesz: nonnegative lattice cosine sum $=|Q(e^{i\omega t})|^2$.
15. Chebyshev: nonnegative $P\not\equiv0$ ⇒ $\cos\theta\,P(\theta)<0$ somewhere (root avoidance in $(-1,0)$).

**E. Analysis of $D$**
16. Explicit formula as density: $\Re W=\int|\hat f|^2\nu_X$, $|\nu_X-\mu|\le3X^2$, $\mu\sim\log|\tau|/2\pi$ ⇒ Gårding.
17. Compactness of low frequencies: mollify, Arzelà–Ascoli, faithfulness of $D$, $|\hat\varphi|\ge\tfrac12$ on $[-T_0,T_0]$.
18. Bessel for $e^{-i\tau u}$ on $[-A,A]$: $\sum_j|\hat e_j(\tau)|^2\le2A$.
19. Convolution representation $\hat f(\tfrac12+a+i\gamma)=\frac1{2\pi}\int\hat\chi(r-ia)\hat f(\gamma-r)dr$ + Lorentzian zero
    mass $O(\log)$ ⇒ local estimate and log-Sobolev upper bound.
20. Depth profile is a positive combination of real exponentials ⇒ rate law by sup of seen depths.

**F. Two variables**
21. Lattice zetas: rank one $n^{-s_1}m^{-s_2}\zeta(s_1+s_2)$, rank two $\zeta(s_1)\zeta(s_2)$; reflection plane gives
    $\Re(s_1+s_2)=1$ and $\xi(s)\xi(1-\bar s)=|\xi(s)|^2$.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Polarization law; spectral model: Rosati ≥ 0 ⇔ unitary; off-circle eigenvectors isotropic | `normSq_eq_of_hasEigenvalue_of_polarization`, `ReflSpectrum.rosatiForm_nonneg_iff_unitary`, `ReflSpectrum.rosatiForm_single` | proved |
| Rosati = collided − defect; Frobenius preserves collided ⇔ unitary | `ReflSpectrum.re_rosatiForm_eq_collided_sub_defect`, `ReflSpectrum.collided_frob_invariant_iff_unitary` | proved |
| Elliptic localizers of an off-line pair are $\mathrm{id}$ and $\sigma_\gamma$ | `affine_mem_pair_iff`, `sigma_eq_tau_comp_fe_comp_tau` | proved |
| Boost + swap blind a pair; Hecke + $\sigma_\gamma$ blind | `eq_zero_of_boost_swap_nonneg`, `hecke_swap_blind` | proved |
| Twist identity; quartet at $\gamma$ collides to real pair | `W_twist`, `shift_quartet` | proved |
| Twisted explicit formula; every off-axis localizer gauge charged | `twisted_explicit_formula`, `exists_vonMangoldt_pos_cos_neg` | proved |
| Below the conductor horizon twisted positivity is a source-blind theorem | `elliptic_sector_nonneg_below_conductor_horizon` | proved |
| Odd sector forces an off-line companion; even sector never forces | `odd_sector_nonneg_forces_offLine_companion`, `even_sector_summand_nonneg` | proved |
| First gauge charge = $\zeta$ at height $\pi/\log2$; second is not a twist | `liouville_window_eq_zeta_twisted`, `not_twist_flips_two_and_three` | proved |
| Global collision has no analytic carrier | `zeta_global_collision_not_analytic` | proved |
| Couplings: kernel counts are modulus squares; height coupling collides evenly | `couple_detDeg_eq_normSq`, `heightCoupled_order_even` | proved |
| Escape forms are Pick forms of the conjugate exterior divisor | `escapeForm_eq_exteriorCauchyForm`, `exteriorCauchyForm_pos` | proved |
| $\Re W=D-\Delta$; $\Re W\le D$ | `re_W_eq_collided_sub_defect`, `re_W_le_collided` | proved |
| RH ⇔ $\Re W=D$ on real tests | `riemannHypothesis_iff_W_eq_collided` | proved |
| $W$ Hecke-invariant always; RH ⇔ $D$ Hecke-invariant ⇔ $T_L$ a similitude of $D$ | `W_translate_translate`, `riemannHypothesis_iff_collided_hecke_invariant`, `hecke_similitude_iff` | proved |
| $D$ faithful; coercive at aperture 3/10 | `collidedForm_eq_zero_iff`, `collidedForm_ge_of_aperture_le_threeTenths` | proved |
| Rate law: $\frac1L\log D(T_Lf)\to2a_f$ | `tendsto_log_depthProfile_div` | proved |
| Local Weyl law: $D(e^{-i\gamma u}f)\asymp\log|\gamma|$, lower constant $\|f\|_2^2$ | `eventually_collidedForm_twist_ge`, `eventually_collidedForm_twist_le` | proved |
| Gårding: $\Re W\ge2\pi\|f\|^2-K\,\mathrm{lowMass}$ | `re_W_ge_sub_lowMass`, `collidedForm_ge_sub_lowMass` | proved |
| $D$ coercive at every aperture (zeros sample every Paley–Wiener space) | `exists_collidedForm_coercive` | proved |
| $W$ has $<2AT_0K/\pi+1$ negative orthonormal directions per aperture | `card_negative_orthonormal_le` | proved |
| $D\asymp\int|\hat f|^2\log(|\sigma|+4)$ at every aperture | `collidedForm_equiv_logSobolev` | proved |
| Leading line of a positive configuration is $\ge0$ and itself positive | `leadingSum_nonneg`, `posDef_leadingLine` | proved |
| Positive configurations ⇔ nonnegative exponential polynomials; one section decides | `posDef_polarSum_iff_scaleWeight_nonneg`, `posDef_section_iff_scaleWeight_nonneg` | proved |
| Positive lattice lines are Hermitian squares (couplings) | `posDef_latticeLine_iff_normSq`, `leadingSum_eq_normSq` | proved |
| Line hierarchy: a line is ≥ 0 where all higher lines vanish | `leadingSum_nonneg_of_higher_eq_zero`, `secondLine_nonneg_of_lattice` | proved |
| Fejér barrier: no harmonic lift removes a lifted deepest quartet | `not_removes_lifted_divisor` | proved |
| Coupled rigidity at $\gamma$ excludes zeros at $\gamma$; at all $\gamma$ gives RH | `xi_ne_zero_of_rigid`, `riemannHypothesis_of_forall_rigid` | proved |
| Twists are rate neutral | `twisted_growth_iff` | proved |
| Diagonal collapse on the square of $\operatorname{Spec}\mathbb Z$ | `rankOne_latticeZeta`, `riemannZeta_reflection_plane_diagonal_ne_zero`, `xi_mul_xi_reflection_plane` | proved |

## 6. Tools

**Developed**
- Spectral model `ReflSpectrum` with Rosati/collided/defect forms; battery `goldenSpectrum_fails`,
  `complexFakeSpectrum_fails`, `golden_detDeg_neg_couple_nonneg`.
- Test calculus: `tr_twist`, `tr_fe`, `tr_sigmaTest`, `tr_translate`, `paperFT_twist`, `weilTest_twist`,
  `twist_eq_heightShift`.
- Polar-configuration kit: `polarScaleWeight_eq_leading`, `tendsto_offLeadingSum`, `quadForm_polarSum_eq_integral`,
  `posDef_polarSum_of_line`, `polarScaleWeight_split`, `exists_cos_mul_neg`, `harmonicLift_leading`.
- Analysis of $D$: `zeta_summable_collided`, `collidedForm_twist_le`, `collidedForm_twist_ge`, `paperFT_mollify`,
  `exists_uniform_subseq`, `tendsto_lowMass_subseq`, `sum_norm_sq_paperFT_le`, `tr_eq_integral_conv`,
  `normSq_tr_le_local`, `exists_log_le_nuX`, `collidedForm_second_difference`.

**To build**
- An arithmetic computation of $D$ or $\Delta$ (the global collision) not using the zeros.
- Odd-sector positivity of the twisted form between the conductor horizon $\log\log\gamma$ and the spacing scale $\log\gamma$.
- A two-variable (non-meromorphic) structure colliding conjugate pairs with odd multiplicity at all ordinates.
- A two-variable section theory with rank growing in the class and a Riemann–Roch whose quadratic term is $W$.
- Effective constants in coercivity and in the log-Sobolev equivalence.

## 7. Open questions

1. Can $\Delta\le D$ be proved from a structure that computes $D$? (This is $W\ge0$.)
2. Does the odd sector force beyond the conductor horizon?
3. Is there an equivariant positive form obtained from counting, and how does it relate to $D$?
4. Is the coupled class `HeightCoupledSystem 2 1 1 γ` rigid at any ordinate by an argument not using zeros at $\gamma$?
5. On the first-twin window: does $W_\zeta(f)$ separate from $W_\zeta(e^{-i\pi u/\log2}f)+\Delta_{\rm arch}+\Delta_{\rm pole}$?
6. Is there an incommensurable-ordinate positive completion that collides oddly?
7. What is the sharp count of negative directions of $W$ at aperture $A$?

## 8. Traps

| Trap | Fact |
|---|---|
| An elliptic symmetry gives a positivity that excludes a zero | Elliptic fibres are definite; only the odd sector forces |
| The functional equation is the elliptic localizer | Only at ordinate $0$; at $\gamma$ it is conjugated by the archimedean flow |
| Elliptic localization is free | Gauge-charged prime side and a conductor $\log\gamma$ |
| Hecke separation combines with elliptic symmetry | Boost + swap at one pair blind it |
| The polarization over $\mathbb Z$ is missing | $D$ exists, is positive, faithful, coercive; its equivariance is RH |
| $W\ge0$ is weaker than $W=D$ | Equivalent for $\zeta$; the defect is the whole content |
| The explicit formula computes $D$ | $D=\sum|\hat f(\rho)|^2$ is not $\sum H(\rho)$ with $H$ holomorphic |
| Squaring the explicit formula collides all pairs | No analytic function carries the global collision |
| A collision producing a real point can be counted | Couplings collide evenly; their counts are modulus squares |
| A two-variable lattice count is a surface count | It collapses to the diagonal or factors |
| A positive completion of a charged weight removes the quartet | Leading line $2m\cos\theta P(\theta)$ is negative somewhere |
| Twisting amplifies | It moves ordinates, keeps every depth |
| Escape positivity excludes zeros | Escape kernels are collided forms, positive by construction |
| The Liouville twin differs arithmetically on the first window | It is $\zeta$ at height $\pi/\log2$ plus archimedean/polar terms |
| Coercivity of $W$ fails badly off RH | $W$ fails in at most finitely many directions per aperture |

## 9. Context

| Uses | Modules |
|---|---|
| RHTower | 15 (explicit formula, Littlewood/Stirling, Lorentzian zero mass, CHMD, Levinson) |
| ArithmeticCorrespondencePositivity | 7 (local form, isometries, height coupling, escape rank, kernel counts) |
| ArithmeticCastelnuovoSeveri | 4 (infinite genus, Fourier inversion, zero-density filtering) |
| HTGeometry | 3 (Bohr AP, Fejér–Riesz, PD Laplace weights) |
| SquareRootThreshold | 2 (window certificates, height shift) |
| StripBochnerWeilForcing, arithmetic-positivity-theory | 1 each (completed systems; single-height detection) |
| Zeta23 (external) | `ZeroConfig`, `W`, `paperFT`, `paperInputs_zeta` |

| Used by | Modules |
|---|---|
| ConjugateDiagonalGeometry | 2 (`ZetaDepthDistribution` uses Hecke invariance of $D$; `SourceMovedTests` uses twists) |

| Neighbour | Relation |
|---|---|
| ArithmeticCorrespondencePositivity | supplies hyperbolic/unipotent types; APol adds elliptic and collided types and the two forms |
| ArithmeticCorrelationGeometry | gauge torus; APol shows the first gauge charge is an archimedean twist and the second is not |
| BiarithmeticGaugeGeometry | non-rigidity of height-coupled systems (counterpart of `CoupledRigid`) |
| arithmetic-positivity-theory, SquareRootThreshold | single-height detection and conductor horizon; APol places them in the odd/even sectors |
| ConjugateDiagonalGeometry | continues the depth distribution and the collided form |
| ArithmeticCastelnuovoSeveri | Rosati = orbit Hodge index; APol isolates the polarization law itself |

## 10. Big picture

Weil's argument needs a form that is positive and equivariant at once. Over $\mathbb Z$ the test space of $\zeta$ carries
two forms, each with exactly one property: Weil's form is equivariant and its positivity is RH; the collided form is
positive, faithful, coercive at every aperture and equal to a logarithmic Sobolev norm, and its equivariance is RH. RH is
the statement that the two coincide. The polarization exists; what is missing is a way to compute it, because the
collided form is the global collision of conjugate zeros, which no analytic object carries and the explicit formula does
not see.

Every attempted repair runs into a structural parity. Localizing at an off-line pair without hyperbolicity forces the
point reflection, which is a twist: it costs a conductor and gauge charge, and only its odd half can force. Positive
completions are couplings: they collide evenly and cannot remove a lifted quartet. For the RH programme this pins the
target: a non-meromorphic, two-variable or measure-valued structure that computes the off-line defect, or that collides
conjugate zeros with odd multiplicity. More positivity built from symmetry or completion cannot reach it.
